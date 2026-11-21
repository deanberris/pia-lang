#!/usr/bin/env python3
"""The proof build-time benchmark (ADR 0032).

Verifies every file in corpus.txt with `piac --verify --verify-stats`, once
on one solver thread and once on every core, and compares the result with a
checked-in baseline:

    python3 tools/bench/proof_bench.py --piac bazel-bin/tools/piac/piac \\
        --baseline tools/bench/baseline.json --out bench.json

Two numbers are tracked per file:

* cost: Z3's deterministic resource count over every query. It does not
  depend on the machine or on how busy it is, so it is gated tightly
  (--cost-threshold, 10% by default). A slower encoding shows up here first.
* wall time, on one thread and on all cores. It depends on the machine, so
  it is gated (--wall-threshold) only against a baseline recorded on the
  same host label (--host).

The run also checks that the report is identical on one thread and on
many, and the cost within 5%: parallel proving must not change any result.

--write-baseline records the current numbers instead of comparing.
Exit status: 0 if within the thresholds, 1 on a regression or a
nondeterministic result, 2 on a usage error.
"""
import argparse
import glob
import json
import os
import platform
import re
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
RLIMIT = 1200000000  # as pia_object passes (tools/piac/pia.bzl)
TIMEOUT_MS = 600000


def corpus(path):
    files = []
    for line in open(path):
        line = line.split("#", 1)[0].strip()
        if not line:
            continue
        matches = sorted(glob.glob(os.path.join(ROOT, line)))
        if not matches:
            sys.exit("proof_bench: %s matches no file" % line)
        files += [os.path.relpath(m, ROOT) for m in matches]
    return files


def run(piac, rel, jobs):
    cmd = [piac, "--verify", "--verify-stats", "--jobs=%d" % jobs,
           "--solver-rlimit=%d" % RLIMIT, "--solver-timeout=%d" % TIMEOUT_MS,
           os.path.basename(rel)]
    start = time.monotonic()
    p = subprocess.run(cmd, cwd=os.path.join(ROOT, os.path.dirname(rel)),
                       capture_output=True, text=True)
    wall_ms = (time.monotonic() - start) * 1000.0
    m = re.search(r"^verify-stats: (.*)$", p.stderr, re.M)
    if not m:
        sys.exit("proof_bench: no stats from %s (exit %d):\n%s"
                 % (rel, p.returncode, p.stderr))
    stats = {k: int(v) for k, v in (kv.split("=") for kv in m.group(1).split())}
    return stats, wall_ms, p.stdout


def measure(piac, files, cores):
    result = {}
    nondeterministic = []
    for rel in files:
        one, wall1, report1 = run(piac, rel, 1)
        many, walln, reportn = run(piac, rel, cores)
        # Z3's resource count varies by about 1% between runs, since some of
        # its hash tables depend on memory addresses; the report may not vary.
        if report1 != reportn or abs(one["cost"] - many["cost"]) > 0.05 * max(one["cost"], 1):
            nondeterministic.append(rel)
        result[rel] = {
            "goals": one["goals"],
            "solved": one["solved"],
            "cost": one["cost"],
            "wall_ms_1": round(wall1, 1),
            "wall_ms_n": round(walln, 1),
            "solve_ms_1": one["solve_ms"],
            "solve_ms_n": many["solve_ms"],
        }
        print("%-36s goals %4d  cost %13d  1 thread %9.0f ms  %d threads %9.0f ms"
              % (rel, one["goals"], one["cost"], wall1, cores, walln),
              file=sys.stderr)
    return result, nondeterministic


def totals(files):
    keys = ["goals", "solved", "cost", "wall_ms_1", "wall_ms_n"]
    return {k: round(sum(f[k] for f in files.values()), 1) for k in keys}


def pct(new, old):
    return (new - old) / old * 100.0 if old else 0.0


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--piac", required=True)
    ap.add_argument("--corpus", default=os.path.join(ROOT, "tools/bench/corpus.txt"))
    ap.add_argument("--baseline", default=os.path.join(ROOT, "tools/bench/baseline.json"))
    ap.add_argument("--out", help="write this run's numbers here, as JSON")
    ap.add_argument("--summary", help="append a Markdown table here "
                    "(such as $GITHUB_STEP_SUMMARY)")
    ap.add_argument("--write-baseline", action="store_true")
    ap.add_argument("--cost-threshold", type=float, default=0.10)
    ap.add_argument("--wall-threshold", type=float, default=None)
    ap.add_argument("--host", default=platform.node())
    ap.add_argument("--jobs", type=int, default=0,
                    help="threads for the parallel run; 0 for every core")
    args = ap.parse_args()

    piac = os.path.abspath(args.piac)
    cores = args.jobs or os.cpu_count() or 1
    files, nondeterministic = measure(piac, corpus(args.corpus), cores)
    run_data = {"host": args.host, "cores": cores, "files": files,
                "total": totals(files)}
    if args.out:
        with open(args.out, "w") as f:
            json.dump(run_data, f, indent=2, sort_keys=True)
            f.write("\n")
    if args.write_baseline:
        with open(args.baseline, "w") as f:
            json.dump(run_data, f, indent=2, sort_keys=True)
            f.write("\n")
        print("proof_bench: wrote %s" % args.baseline, file=sys.stderr)
        return 0

    base = json.load(open(args.baseline))
    failures = ["%s: the report or the cost differs between 1 and %d threads"
                % (rel, cores) for rel in nondeterministic]
    same_host = base.get("host") == args.host
    rows = []
    for rel, now in files.items():
        old = base["files"].get(rel)
        if old is None:
            rows.append((rel, now, None, "new"))
            continue
        notes = []
        if now["cost"] > old["cost"] * (1 + args.cost_threshold):
            notes.append("cost +%.1f%%" % pct(now["cost"], old["cost"]))
        if args.wall_threshold is not None and same_host:
            for k in ("wall_ms_1", "wall_ms_n"):
                # Under 100 ms the noise is larger than any regression.
                if old[k] >= 100 and now[k] > old[k] * (1 + args.wall_threshold):
                    notes.append("%s +%.1f%%" % (k, pct(now[k], old[k])))
        if notes:
            failures.append("%s: %s" % (rel, ", ".join(notes)))
        rows.append((rel, now, old, ", ".join(notes) or "ok"))

    t, bt = run_data["total"], base["total"]
    lines = ["### Proof build time", "",
             "%d files, %d goals, %d solver queries. Cost %d (baseline %d, %+.1f%%). "
             "Wall time %.0f ms on 1 thread, %.0f ms on %d (%.1fx)."
             % (len(files), t["goals"], t["solved"], t["cost"], bt["cost"],
                pct(t["cost"], bt["cost"]), t["wall_ms_1"], t["wall_ms_n"], cores,
                t["wall_ms_1"] / t["wall_ms_n"] if t["wall_ms_n"] else 0),
             "",
             "| file | goals | cost | vs baseline | 1 thread (ms) | %d threads (ms) | status |"
             % cores,
             "| --- | ---: | ---: | ---: | ---: | ---: | --- |"]
    for rel, now, old, status in rows:
        vs = "%+.1f%%" % pct(now["cost"], old["cost"]) if old else "new"
        lines.append("| %s | %d | %d | %s | %.0f | %.0f | %s |"
                     % (rel, now["goals"], now["cost"], vs, now["wall_ms_1"],
                        now["wall_ms_n"], status))
    if not same_host:
        lines += ["", "Wall times are not gated: the baseline was recorded on %s."
                  % base.get("host")]
    text = "\n".join(lines) + "\n"
    print(text)
    if args.summary:
        with open(args.summary, "a") as f:
            f.write(text)
    for f in failures:
        print("proof_bench: regression: " + f, file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
