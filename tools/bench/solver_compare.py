#!/usr/bin/env python3
"""Compares SMT solvers on the queries piac sends to Z3 (ADR 0066).

    piac --dump-smt --solver-cost file.pia 2> dump.txt
    python3 tools/bench/solver_compare.py split dump.txt out/
    python3 tools/bench/solver_compare.py run out/ --timeout 30 \\
        --solvers z3,z3-intblast,cvc5-intblast
    python3 tools/bench/solver_compare.py summary out/

`split` writes one .smt2 file per query, with an index of where each came
from. `run` solves each with each solver, four at a time, and keeps the
results in out/results.json, so an interrupted run picks up where it
stopped. `summary` prints, per solver, how many queries were proved and
how long they took, and what routing nonlinear queries to int-blasting
(and the rest to Z3's bit-blaster) would take.

Solvers: `z3` (Z3's default solver, as piac calls it), `z3-intblast` (the
`smt` tactic with `smt.bv.solver=2`), and, if installed,
`cvc5-intblast` (`--solve-bv-as-int=sum`), `cvc5` and `bitwuzla`. Set
Z3, CVC5 and BITWUZLA to their binaries. No GPL-licensed solver is
supported (ADR 0066).
"""

import argparse
import collections
import json
import os
import re
import subprocess
import sys
import time
from concurrent.futures import ThreadPoolExecutor

HEADER = re.compile(r"^; (\S+:\d+:\d+): (.*)$")
NONLINEAR = re.compile(r"\((bvmul|bvsdiv|bvsrem|bvudiv|bvurem) (\S+) (\S+?)\)")


def literal(term):
    return term.startswith("#") or term.startswith("(_")


def nonlinear(text):
    """The rule piac uses (multipliesVariables), on let-bound operands."""
    for m in NONLINEAR.finditer(text):
        a, b = m.group(2), m.group(3)
        if m.group(1) == "bvmul":
            if not literal(a) and not literal(b):
                return True
        elif not literal(b):
            return True
    return False


def split(args):
    os.makedirs(args.out, exist_ok=True)
    goals, cur = [], None
    for line in open(args.dump, errors="replace"):
        m = HEADER.match(line)
        if m:
            cur = {"where": m.group(1), "claim": m.group(2), "body": []}
            goals.append(cur)
        elif cur is not None and (line[:1] in (";", "(", " ", ")") or not line.strip()):
            cur["body"].append(line)
        else:
            cur = None  # a report line: the query has ended
    index = []
    for i, g in enumerate(goals):
        body = "".join(g["body"]).strip()
        if "(assert" not in body:
            continue
        if "check-sat" not in body:
            body += "\n(check-sat)"  # piac asks for the result separately
        name = "g%04d.smt2" % i
        with open(os.path.join(args.out, name), "w") as f:
            f.write(body + "\n")
        index.append({"file": name, "where": g["where"], "claim": g["claim"]})
    with open(os.path.join(args.out, "index.json"), "w") as f:
        json.dump(index, f, indent=1)
    print(len(index), "queries")


def solve_one(solver, path, timeout):
    text = open(path).read()
    plain = re.sub(r"\(check-sat-using .*\)\s*$", "(check-sat)", text, flags=re.M)
    if solver == "z3":
        cmd, inp = [os.environ.get("Z3", "z3"), "-in", "-smt2", "-T:%d" % timeout], text
    elif solver == "z3-intblast":
        cmd = [os.environ.get("Z3", "z3"), "-in", "-smt2", "-T:%d" % timeout, "smt.bv.solver=2"]
        inp = plain.replace("(check-sat)", "(check-sat-using smt)")
    elif solver in ("cvc5", "cvc5-intblast"):
        cmd = [os.environ.get("CVC5", "cvc5"), "--lang=smt2", "--tlimit-per=%d" % (timeout * 1000)]
        if solver == "cvc5-intblast":
            cmd.append("--solve-bv-as-int=sum")
        inp = plain if "(set-logic" in plain else "(set-logic ALL)\n" + plain
    elif solver == "bitwuzla":
        cmd = [os.environ.get("BITWUZLA", "bitwuzla"), "--time-limit-per=%d" % (timeout * 1000)]
        inp = plain if "(set-logic" in plain else "(set-logic ALL)\n" + plain
    else:
        sys.exit("unknown solver " + solver)
    start = time.time()
    try:
        p = subprocess.run(cmd, input=inp, capture_output=True, text=True, timeout=timeout + 5)
        out = (p.stdout + p.stderr).split()
        result = next((w for w in out if w in ("sat", "unsat", "unknown")), "error")
    except subprocess.TimeoutExpired:
        result = "timeout"
    except FileNotFoundError:
        result = "missing"
    return result, round(time.time() - start, 3)


def run(args):
    index = json.load(open(os.path.join(args.out, "index.json")))
    path = os.path.join(args.out, "results.json")
    results = json.load(open(path)) if os.path.exists(path) else {}
    jobs = [(g["file"], s) for g in index for s in args.solvers.split(",")
            if "%s|%s" % (g["file"], s) not in results]

    def one(job):
        f, s = job
        return job, solve_one(s, os.path.join(args.out, f), args.timeout)

    with ThreadPoolExecutor(args.jobs) as pool:
        for n, ((f, s), r) in enumerate(pool.map(one, jobs)):
            results["%s|%s" % (f, s)] = r
            if n % 20 == 0:
                json.dump(results, open(path, "w"))
    json.dump(results, open(path, "w"), indent=0)


def summary(args):
    index = {g["file"]: g for g in json.load(open(os.path.join(args.out, "index.json")))}
    results = json.load(open(os.path.join(args.out, "results.json")))
    per = collections.defaultdict(dict)
    for k, r in results.items():
        f, s = k.split("|")
        per[f][s] = r
    solvers = sorted({s for r in per.values() for s in r})
    for s in solvers:
        counts = collections.Counter(per[f][s][0] for f in per if s in per[f])
        times = sorted(per[f][s][1] for f in per if s in per[f])
        print("%-14s %s total %.1fs max %.2fs" % (s, dict(counts), sum(times), times[-1]))
    if {"z3", "z3-intblast"} <= set(solvers):
        nl = {f for f in per if nonlinear(open(os.path.join(args.out, f)).read())}
        routed = [per[f]["z3-intblast" if f in nl else "z3"] for f in per]
        counts = collections.Counter(r[0] for r in routed)
        print("routed         %s total %.1fs (%d nonlinear of %d)" %
              (dict(counts), sum(r[1] for r in routed), len(nl), len(per)))
    for f in per:
        answers = {per[f][s][0] for s in per[f]} & {"sat", "unsat"}
        if len(answers) > 1:
            print("DISAGREE", index[f]["where"], {s: per[f][s][0] for s in per[f]})


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    sub = ap.add_subparsers(dest="cmd", required=True)
    p = sub.add_parser("split")
    p.add_argument("dump")
    p.add_argument("out")
    p = sub.add_parser("run")
    p.add_argument("out")
    p.add_argument("--solvers", default="z3,z3-intblast")
    p.add_argument("--timeout", type=int, default=30)
    p.add_argument("--jobs", type=int, default=4)
    p = sub.add_parser("summary")
    p.add_argument("out")
    args = ap.parse_args()
    {"split": split, "run": run, "summary": summary}[args.cmd](args)


if __name__ == "__main__":
    main()
