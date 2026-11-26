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
`--passes=parallel` skips the one-thread run, and with it that check, and
gates the cost of the parallel run: it halves the time, and CI uses it on
pull requests, keeping both passes for the nightly run.

`--shard=K/N` measures only the Kth of N shards of the corpus, balanced by
the baseline's wall times, so CI can run the corpus on N machines at once.
Every shard still emits every library interface, since a file may import
one from another shard. `--only=PATH` (repeatable) measures just those
corpus files.

--write-baseline records the measured files' numbers in the baseline
instead of comparing, keeping the other files' entries; `--merge=FILE`
(repeatable) does the same from the `--out` files of earlier runs, such as
CI's shards, without running piac. Either drops entries for files no
longer in the corpus.
Exit status: 0 if within the thresholds, 1 on a regression or a
nondeterministic result, 2 on a usage error.
"""
import argparse
import glob
import json
import os
import platform
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
RLIMIT = 1200000000  # as pia_object passes (tools/piac/pia.bzl)
TIMEOUT_MS = 600000
IFACE_DIR = None  # the corpus's interfaces, for files that import (ADR 0039)


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
    if IFACE_DIR:
        cmd[1:1] = ["--iface-path=%s" % IFACE_DIR]
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


def interfaces(piac, files):
    """Emits every library module's interface into a scratch directory, so
    a module that imports another, such as Pia.Core.Algo.Search importing
    Pia.Core.Order, verifies as its pia_library rule does. Shallower paths
    go first; a file with no interface is skipped."""
    out = tempfile.mkdtemp(prefix="proof_bench_iface.")
    libs = [f for f in files if f.startswith("lib/")]
    for rel in sorted(libs, key=lambda f: (f.count("/"), f)):
        subprocess.run([piac, "--emit=interface", "-o", out,
                        os.path.join(ROOT, rel)], capture_output=True)
    return out


def shard(files, spec, base):
    """The files of shard K of N (spec "K/N", K from 1): each file, slowest
    first by the baseline's parallel wall time, goes to the shard with the
    least time so far. A file the baseline lacks counts as a second. Every
    shard computes the same split, so together they cover the corpus once."""
    m = re.match(r"^(\d+)/(\d+)$", spec)
    if not m or not 1 <= int(m.group(1)) <= int(m.group(2)):
        sys.exit("proof_bench: --shard wants K/N with 1 <= K <= N, not %s" % spec)
    k, n = int(m.group(1)), int(m.group(2))
    known = base.get("files", {})
    weight = {f: known.get(f, {}).get("wall_ms_n", 1000.0) for f in files}
    load = [0.0] * n
    mine = set()
    for f in sorted(files, key=lambda f: (-weight[f], f)):
        i = min(range(n), key=lambda i: (load[i], i))
        load[i] += weight[f]
        if i == k - 1:
            mine.add(f)
    return [f for f in files if f in mine]


def measure(piac, files, cores, passes):
    result = {}
    nondeterministic = []
    for rel in files:
        many, walln, reportn = run(piac, rel, cores)
        if passes == "both":
            one, wall1, report1 = run(piac, rel, 1)
            # Z3's resource count varies by about 1% between runs, since some
            # of its hash tables depend on memory addresses; the report may
            # not vary.
            if report1 != reportn or abs(one["cost"] - many["cost"]) > 0.05 * max(one["cost"], 1):
                nondeterministic.append(rel)
        else:
            one, wall1 = many, None
        result[rel] = {
            "goals": one["goals"],
            "solved": one["solved"],
            "cost": one["cost"],
            "wall_ms_n": round(walln, 1),
            "solve_ms_n": many["solve_ms"],
        }
        if wall1 is not None:
            result[rel]["wall_ms_1"] = round(wall1, 1)
            result[rel]["solve_ms_1"] = one["solve_ms"]
        print("%-36s goals %4d  cost %13d  1 thread %9s ms  %d threads %9.0f ms"
              % (rel, one["goals"], one["cost"],
                 "%.0f" % wall1 if wall1 is not None else "-", cores, walln),
              file=sys.stderr)
    return result, nondeterministic


def totals(files):
    keys = ["goals", "solved", "cost", "wall_ms_1", "wall_ms_n"]
    return {k: round(sum(f.get(k, 0) for f in files.values()), 1) for k in keys}


def write_baseline(path, base, measured, listed, host, cores):
    """Puts the measured files' numbers into the baseline at `path`, keeps
    the other corpus files' entries, and drops files no longer listed."""
    files = {f: v for f, v in base.get("files", {}).items() if f in listed}
    files.update({f: v for f, v in measured.items() if f in listed})
    data = {"host": host, "cores": cores, "files": files,
            "total": totals(files)}
    with open(path, "w") as f:
        json.dump(data, f, indent=2, sort_keys=True)
        f.write("\n")
    print("proof_bench: wrote %s (%d files, %d measured now)"
          % (path, len(files), len(measured)), file=sys.stderr)


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
    ap.add_argument("--passes", choices=["both", "parallel"], default="both",
                    help="both: one thread, then --jobs, and check they "
                    "agree; parallel: --jobs only")
    ap.add_argument("--shard", help="K/N: measure only the Kth of N shards")
    ap.add_argument("--only", action="append", default=[],
                    help="measure only this corpus file (repeatable)")
    ap.add_argument("--merge", action="append", default=[],
                    help="with --write-baseline: take the numbers from this "
                    "--out file instead of running piac (repeatable)")
    args = ap.parse_args()

    cores = args.jobs or os.cpu_count() or 1
    listed = corpus(args.corpus)
    base = json.load(open(args.baseline)) if os.path.exists(args.baseline) else {}
    if args.merge:
        if not args.write_baseline:
            sys.exit("proof_bench: --merge needs --write-baseline")
        measured = {}
        for path in args.merge:
            measured.update(json.load(open(path))["files"])
        write_baseline(args.baseline, base, measured, set(listed), args.host, cores)
        return 0

    piac = os.path.abspath(args.piac)
    chosen = listed
    if args.only:
        unknown = [f for f in args.only if f not in listed]
        if unknown:
            sys.exit("proof_bench: not in the corpus: %s" % ", ".join(unknown))
        chosen = [f for f in listed if f in args.only]
    if args.shard:
        chosen = shard(chosen, args.shard, base)
    global IFACE_DIR
    IFACE_DIR = interfaces(piac, listed)
    try:
        files, nondeterministic = measure(piac, chosen, cores, args.passes)
    finally:
        shutil.rmtree(IFACE_DIR, ignore_errors=True)
    run_data = {"host": args.host, "cores": cores, "passes": args.passes,
                "shard": args.shard, "files": files, "total": totals(files)}
    if args.out:
        with open(args.out, "w") as f:
            json.dump(run_data, f, indent=2, sort_keys=True)
            f.write("\n")
    if args.write_baseline:
        write_baseline(args.baseline, base, files, set(listed), args.host, cores)
        return 0
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
                if k not in now or k not in old:
                    continue
                # Under 100 ms the noise is larger than any regression.
                if old[k] >= 100 and now[k] > old[k] * (1 + args.wall_threshold):
                    notes.append("%s +%.1f%%" % (k, pct(now[k], old[k])))
        if notes:
            failures.append("%s: %s" % (rel, ", ".join(notes)))
        rows.append((rel, now, old, ", ".join(notes) or "ok"))

    # The baseline's cost over the same files, so a shard compares like
    # with like; files new to the baseline count on neither side.
    t = run_data["total"]
    gated = [r for r in files if r in base["files"]]
    bt = sum(base["files"][r]["cost"] for r in gated)
    nt = sum(files[r]["cost"] for r in gated)
    title = "### Proof build time" + (" (shard %s)" % args.shard if args.shard else "")
    wall = ("Wall time %.0f ms on 1 thread, %.0f ms on %d (%.1fx)."
            % (t["wall_ms_1"], t["wall_ms_n"], cores,
               t["wall_ms_1"] / t["wall_ms_n"] if t["wall_ms_n"] else 0)
            if args.passes == "both" else
            "Wall time %.0f ms on %d threads (one pass)." % (t["wall_ms_n"], cores))
    lines = [title, "",
             "%d files, %d goals, %d solver queries. Cost %d; on the %d files "
             "in the baseline %d against %d (%+.1f%%). %s"
             % (len(files), t["goals"], t["solved"], t["cost"], len(gated),
                nt, bt, pct(nt, bt), wall),
             "",
             "| file | goals | cost | vs baseline | 1 thread (ms) | %d threads (ms) | status |"
             % cores,
             "| --- | ---: | ---: | ---: | ---: | ---: | --- |"]
    for rel, now, old, status in rows:
        vs = "%+.1f%%" % pct(now["cost"], old["cost"]) if old else "new"
        lines.append("| %s | %d | %d | %s | %s | %.0f | %s |"
                     % (rel, now["goals"], now["cost"], vs,
                        "%.0f" % now["wall_ms_1"] if "wall_ms_1" in now else "-",
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
