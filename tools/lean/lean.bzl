"""pia_lean_proof: checks the Lean proofs of a Pia file's lemmas (ADR 0061)."""

def _pia_lean_proof_impl(ctx):
    lean_files = ctx.attr._lean[DefaultInfo].files
    lean = [f for f in lean_files.to_list() if f.path.endswith("/bin/lean")]
    if len(lean) != 1:
        fail("the Lean toolchain has no bin/lean")
    receipt = ctx.actions.declare_file(ctx.label.name + ".receipt")
    args = []
    inputs = [ctx.file.src, ctx.file.proofs]
    transitive = [lean_files]
    if ctx.attr.mathlib:
        oleans = ctx.attr.mathlib[DefaultInfo].files
        rev = [f for f in oleans.to_list() if f.basename == "rev"]
        if len(rev) != 1:
            fail("mathlib must be @mathlib//:oleans, which has a rev file")
        args = ["--mathlib-root", rev[0].dirname]
        transitive.append(oleans)
    ctx.actions.run(
        executable = ctx.executable._lean_proof,
        arguments = [
            "--piac",
            ctx.executable._piac.path,
            "--lean",
            lean[0].path,
            "--src",
            ctx.file.src.path,
            "--proofs",
            ctx.file.proofs.path,
            "--out",
            receipt.path,
        ] + args,
        inputs = depset(inputs, transitive = transitive),
        tools = [ctx.executable._piac],
        outputs = [receipt],
        mnemonic = "PiaLeanProof",
        progress_message = "Checking the Lean proofs of %s" % ctx.file.src.short_path,
        # The toolchain is a few thousand files; running Lean where it was
        # downloaded saves sending them to a remote executor.
        execution_requirements = {"no-remote-exec": "1"},
    )
    return [DefaultInfo(files = depset([receipt]))]

pia_lean_proof = rule(
    implementation = _pia_lean_proof_impl,
    doc = """Checks the Lean proofs of the lemmas of one Pia file proved in Lean.

`src` has lemmas `let lemma l ... = by lean T`. `proofs` is a Lean file that
starts with `import Statements` and proves each `T : <ns>.l`, where `<ns>`
is the module of `src`, or its file name, and `Statements` is what
`piac --emit=lean src` writes. A statement over `real` imports Mathlib, so
its target sets `mathlib = "@mathlib//:oleans"`, and its receipts name the
Mathlib commit with the Lean toolchain. The output, `<name>.receipt`, has a receipt
for each lemma; pass it to `piac --verify --lean-receipt=<file>`. Lean never
runs in piac: a receipt for an older statement is stale, and piac fails its
goal.
""",
    attrs = {
        "src": attr.label(allow_single_file = [".pia", ".pia.md"], mandatory = True),
        "proofs": attr.label(allow_single_file = [".lean"], mandatory = True),
        "mathlib": attr.label(doc = "@mathlib//:oleans, for proofs that import Mathlib."),
        "_piac": attr.label(default = "//tools/piac", executable = True, cfg = "exec"),
        "_lean_proof": attr.label(default = "//tools/lean:lean_proof", executable = True, cfg = "exec"),
        "_lean": attr.label(default = "//third_party/lean:lean", cfg = "exec"),
    },
)

def _lean_check_test_impl(ctx):
    lean_files = ctx.attr._lean[DefaultInfo].files
    lean = [f for f in lean_files.to_list() if f.path.endswith("/bin/lean")]
    if len(lean) != 1:
        fail("the Lean toolchain has no bin/lean")
    log = ctx.actions.declare_file(ctx.label.name + ".log")
    # Lean fails on an error; `#print axioms` lines that name sorryAx mean
    # a proof was left out, which fails too.
    ctx.actions.run_shell(
        command = """
set -e
"$1" "$2" > "$3" 2>&1 || { cat "$3"; exit 1; }
if grep -q sorryAx "$3"; then cat "$3"; echo "error: a proof uses sorry"; exit 1; fi
""",
        arguments = [lean[0].path, ctx.file.src.path, log.path],
        inputs = depset([ctx.file.src], transitive = [lean_files]),
        outputs = [log],
        mnemonic = "LeanCheck",
        progress_message = "Checking the Lean proofs in %s" % ctx.file.src.short_path,
        execution_requirements = {"no-remote-exec": "1"},
    )
    script = ctx.actions.declare_file(ctx.label.name + ".sh")
    ctx.actions.write(script, "#!/bin/sh\ncat '%s'\n" % log.short_path, is_executable = True)
    return [DefaultInfo(executable = script, runfiles = ctx.runfiles(files = [log]))]

lean_check_test = rule(
    implementation = _lean_check_test_impl,
    test = True,
    doc = """Checks a self-contained Lean 4 file, with no Mathlib.

The check runs when the test is built: Lean must accept `src`, and no
`#print axioms` line in its output may name `sorryAx`. The test prints
Lean's output, the axioms each theorem depends on.
""",
    attrs = {
        "src": attr.label(allow_single_file = [".lean"], mandatory = True),
        "_lean": attr.label(default = "//third_party/lean:lean", cfg = "exec"),
    },
)
