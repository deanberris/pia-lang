#!/usr/bin/env python3
"""The codegen benchmark (ADR 0075): Pia against C, C++, Rust and Zig.

Runs every program of every problem in bench/codegen/problems.json, as built
by `bazel build //bench/codegen/...`, and reports two numbers per program:

* instructions: cachegrind's instruction count (`valgrind --tool=cachegrind
  --cache-sim=no`) on the problem's smaller `count_args`. It does not depend
  on the machine's load, so it can be compared across commits, as the proof
  benchmark compares Z3's rlimit. Skipped where valgrind is missing (macOS).
* wall time: the median of --runs runs on the problem's `args`, after one
  warm-up run. It depends on the machine, so it is only reported.

Each program is also given as a ratio to the problem's `reference` (plb2's
C, for nqueen). The summary's codegen number is the geometric mean of Pia
against the same algorithm in C: the problem's `control` where the proof made
the port differ from the reference (ADR 0075, section 1), else the reference.

    python3 tools/bench/codegen_bench.py --bazel-bin bazel-bin \\
        --out codegen.json --summary codegen.md

With --baseline, instruction counts are compared with a checked-in baseline
and the change is reported. Nothing fails on a change yet: ADR 0075 gates at
+5% only once wave 1 is complete (Dean, 2026-11-27). --write-baseline
records this run's instruction counts as the baseline instead.

Exit status: 0 when every program ran and printed its problem's answer, 1
when one failed or printed something else, 2 on a usage error.
"""
import argparse
import json
import math
import os
import platform
import re
import shutil
import statistics
import subprocess
import sys
import tempfile
import time

ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
PROBLEMS = os.path.join(ROOT, "bench", "codegen", "problems.json")


def run_output(path, args):
    """The program's stdout and stderr together: plb2's Zig prints to stderr."""
    proc = subprocess.run([path] + args, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True, check=False)
    return proc.returncode, proc.stdout.strip()


def wall_times(path, args, runs):
    run_output(path, args)  # warm-up
    times = []
    for _ in range(runs):
        start = time.perf_counter()
        subprocess.run([path] + args, stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL, check=False)
        times.append(time.perf_counter() - start)
    return times


def instructions(valgrind, path, args):
    with tempfile.TemporaryDirectory() as tmp:
        proc = subprocess.run(
            [valgrind, "--tool=cachegrind", "--cache-sim=no",
             "--cachegrind-out-file=" + os.path.join(tmp, "out"), path] + args,
            stdout=subprocess.DEVNULL, stderr=subprocess.PIPE, text=True,
            check=False)
    match = re.search(r"I\s+refs:\s+([\d,]+)", proc.stderr)
    return int(match.group(1).replace(",", "")) if match else None


def host_label():
    if sys.platform == "darwin":
        chip = subprocess.run(["sysctl", "-n", "machdep.cpu.brand_string"],
                              stdout=subprocess.PIPE, text=True, check=False)
        return chip.stdout.strip() or "macOS " + platform.machine()
    try:
        with open("/proc/cpuinfo", encoding="utf-8") as cpuinfo:
            for line in cpuinfo:
                if line.startswith("model name"):
                    return line.split(":", 1)[1].strip()
    except OSError:
        pass
    return platform.machine()


def measure(args, problems):
    valgrind = None if args.no_count else shutil.which("valgrind")
    failed = False
    results = {}
    for name, problem in problems.items():
        if args.only and name not in args.only:
            continue
        entry = {"args": problem["args"], "count_args": problem["count_args"],
                 "reference": problem["reference"], "programs": {}}
        for program in problem["programs"]:
            path = os.path.join(args.bazel_bin, "bench", "codegen", name,
                                "%s_%s" % (name, program))
            if not os.path.exists(path):
                print("missing: %s (bazel build //bench/codegen/...)" % path,
                      file=sys.stderr)
                failed = True
                continue
            status, out = run_output(path, problem["count_args"])
            if status != 0 or out != problem["count_expected"]:
                print("%s %s: printed %r (status %d), expected %r" %
                      (name, program, out, status, problem["count_expected"]),
                      file=sys.stderr)
                failed = True
                continue
            row = {}
            if valgrind:
                row["instructions"] = instructions(valgrind, path,
                                                   problem["count_args"])
            if args.runs > 0:
                times = wall_times(path, problem["args"], args.runs)
                row["wall_s"] = statistics.median(times)
                row["wall_min_s"] = min(times)
                row["wall_max_s"] = max(times)
            entry["programs"][program] = row
            print("%s %s: %s" % (name, program, row), file=sys.stderr)
        results[name] = entry
    return results, failed


def ratio(results, problem, program, key, against=None):
    rows = results[problem]["programs"]
    ref = rows.get(against or results[problem]["reference"], {}).get(key)
    value = rows.get(program, {}).get(key)
    if not ref or not value:
        return None
    return value / ref


def summary(report, baseline):
    lines = ["## Codegen benchmark (ADR 0075)", "",
             "Host: %s. Ratios are to each problem's reference program; "
             "instructions are cachegrind's count on the smaller input." %
             report["host"], ""]
    lines.append("| Problem | Program | Instructions | vs reference | vs baseline "
                 "| Wall time (s) | vs reference |")
    lines.append("| --- | --- | ---: | ---: | ---: | ---: | ---: |")
    pia_ratios = []
    for name, entry in report["problems"].items():
        for program, row in entry["programs"].items():
            count = row.get("instructions")
            count_ratio = ratio(report["problems"], name, program, "instructions")
            wall_ratio = ratio(report["problems"], name, program, "wall_s")
            if program == "pia":
                same = "control" if "control" in entry["programs"] else None
                codegen = (ratio(report["problems"], name, "pia", "instructions", same)
                           or ratio(report["problems"], name, "pia", "wall_s", same))
                if codegen:
                    pia_ratios.append(codegen)
            base = (baseline.get(name, {}).get(program, {}).get("instructions")
                    if baseline else None)
            lines.append("| %s | %s | %s | %s | %s | %s | %s |" % (
                name, program,
                "{:,}".format(count) if count else "",
                "%.3f" % count_ratio if count_ratio else "",
                "%+.2f%%" % (100.0 * (count - base) / base) if count and base else "",
                "%.3f" % row["wall_s"] if "wall_s" in row else "",
                "%.3f" % wall_ratio if wall_ratio else ""))
    if pia_ratios:
        mean = math.exp(sum(math.log(r) for r in pia_ratios) / len(pia_ratios))
        lines += ["", "Codegen: the geometric mean of Pia against the same "
                  "algorithm in C (the control where there is one) is %.3f, "
                  "over %d problems." % (mean, len(pia_ratios))]
    lines += ["", "Report only: nothing gates until wave 1 is complete."]
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    parser.add_argument("--bazel-bin", default=os.path.join(ROOT, "bazel-bin"))
    parser.add_argument("--problems", default=PROBLEMS)
    parser.add_argument("--only", action="append", default=[],
                        help="measure only this problem (repeatable)")
    parser.add_argument("--runs", type=int, default=10,
                        help="timed runs per program; 0 skips wall time")
    parser.add_argument("--no-count", action="store_true",
                        help="skip the cachegrind instruction counts")
    parser.add_argument("--baseline",
                        default=os.path.join(ROOT, "bench", "codegen", "baseline.json"))
    parser.add_argument("--write-baseline", action="store_true")
    parser.add_argument("--out", help="write the JSON report here")
    parser.add_argument("--summary", help="write a Markdown summary here")
    args = parser.parse_args()

    with open(args.problems, encoding="utf-8") as f:
        problems = json.load(f)
    results, failed = measure(args, problems)
    report = {"host": host_label(), "problems": results}

    baseline = {}
    if os.path.exists(args.baseline):
        with open(args.baseline, encoding="utf-8") as f:
            baseline = json.load(f).get("problems", {})
    if args.write_baseline:
        for name, entry in results.items():
            baseline[name] = {program: {"instructions": row["instructions"]}
                              for program, row in entry["programs"].items()
                              if row.get("instructions")}
        with open(args.baseline, "w", encoding="utf-8") as f:
            json.dump({"host": report["host"], "problems": baseline}, f,
                      indent=2, sort_keys=True)
            f.write("\n")

    if args.out:
        with open(args.out, "w", encoding="utf-8") as f:
            json.dump(report, f, indent=2, sort_keys=True)
            f.write("\n")
    text = summary(report, baseline)
    if args.summary:
        with open(args.summary, "w", encoding="utf-8") as f:
            f.write(text)
    print(text)
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
