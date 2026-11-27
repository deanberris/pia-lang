"""Checks the Lean proofs of a Pia file's lemmas and writes their receipts.

The pia_lean_proof rule (tools/lean/lean.bzl) runs this once per Pia file
that has lemmas proved in Lean, `let lemma l ... = by lean T` (ADR 0061):

1. `piac --emit=lean` writes Statements.lean, the lemmas' statements and the
   spec functions and record types they use, with each statement's hash.
2. Lean compiles Statements.lean, then the proofs, which `import Statements`.
3. A last file checks that each theorem `T` has the type of its statement,
   `example : <ns>.l := T`, and prints the axioms `T` depends on.
4. Each statement whose proof checks, with only the standard axioms, gets a
   receipt: its lemma, statement hash, theorem, toolchain and axioms. piac
   reads them with --lean-receipt and fails a lemma whose receipt is
   missing or stale.

Usage: lean_proof.py --piac <piac> --lean <bin/lean> --src <file.pia>
                     --proofs <Proofs.lean> --out <file.receipt>
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile

# The axioms a receipt may list. `propext`, `Classical.choice` and
# `Quot.sound` are Lean's own. `Lean.ofReduceBool` and `Lean.trustCompiler`
# come from `native_decide`, which trusts the compiler, so the trust report
# lists them (ADR 0061, section 2). Anything else, `sorryAx` above all, is
# not a proof.
ALLOWED_AXIOMS = {
    "propext",
    "Classical.choice",
    "Quot.sound",
    "Lean.ofReduceBool",
    "Lean.trustCompiler",
}


def run(args, cwd, env, what):
    r = subprocess.run(args, cwd=cwd, env=env, capture_output=True, text=True)
    if r.returncode != 0:
        sys.stderr.write(f"lean_proof: {what} failed:\n{r.stdout}{r.stderr}")
        sys.exit(1)
    return r.stdout


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--piac", required=True)
    p.add_argument("--lean", required=True)
    p.add_argument("--src", required=True)
    p.add_argument("--proofs", required=True)
    p.add_argument("--out", required=True)
    a = p.parse_args()

    lean = os.path.abspath(a.lean)
    work = tempfile.mkdtemp(prefix="pia_lean_")
    try:
        env = dict(os.environ, LEAN_PATH=work)
        statements = os.path.join(work, "Statements.lean")
        run([os.path.abspath(a.piac), "--emit=lean", "-o", statements,
             os.path.abspath(a.src)], work, env, "piac --emit=lean")
        with open(statements) as f:
            text = f.read()
        lemmas = re.findall(r"^-- pia-lean-statement (\S+) (\S+) ([0-9a-f]{64})$",
                            text, flags=re.M)
        ns = re.search(r"^namespace (\S+)$", text, flags=re.M)
        if not lemmas or not ns:
            sys.stderr.write(f"lean_proof: {a.src} has no lemma proved in Lean\n")
            return 1
        ns = ns.group(1)

        # Lean names a module after its path from the working directory.
        run([lean, "-o", "Statements.olean", "Statements.lean"], work, env,
            "Lean on the statements")
        shutil.copyfile(a.proofs, os.path.join(work, "Proofs.lean"))
        run([lean, "-o", "Proofs.olean", "Proofs.lean"], work, env,
            f"Lean on {a.proofs}")

        check = ["import Statements", "import Proofs", ""]
        for lemma, theorem, _ in lemmas:
            check.append(f"example : {ns}.{lemma} := {theorem}")
            check.append(f"#print axioms {theorem}")
        with open(os.path.join(work, "Check.lean"), "w") as f:
            f.write("\n".join(check) + "\n")
        out = run([lean, "Check.lean"], work, env,
                  "checking the theorems against the statements")

        version = run([lean, "--version"], work, env, "lean --version")
        m = re.search(r"version (\d+\.\d+\.\d+)", version)
        toolchain = "leanprover/lean4:v" + (m.group(1) if m else "unknown")

        receipts = []
        for lemma, theorem, digest in lemmas:
            q = re.escape(theorem)
            if re.search(rf"'{q}' does not depend on any axioms", out):
                axioms = []
            else:
                m = re.search(rf"'{q}' depends on axioms: \[([^\]]*)\]", out)
                if not m:
                    sys.stderr.write(f"lean_proof: no axioms reported for {theorem}:\n{out}")
                    return 1
                axioms = [x.strip() for x in m.group(1).split(",") if x.strip()]
            bad = [x for x in axioms if x not in ALLOWED_AXIOMS]
            if bad:
                sys.stderr.write(f"lean_proof: the proof of {lemma}, {theorem}, "
                                 f"depends on {', '.join(bad)}, so it proves nothing\n")
                return 1
            receipts.append("\n".join([
                "pia-lean-receipt 1",
                f"lemma {lemma}",
                f"statement {digest}",
                f"theorem {theorem}",
                f"toolchain {toolchain}",
                "axioms " + " ".join(axioms),
            ]) + "\n")
        with open(a.out, "w") as f:
            f.write("\n".join(receipts))
        return 0
    finally:
        shutil.rmtree(work, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
