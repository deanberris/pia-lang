"""Bazel rules for compiling Pia programs with piac."""

def pia_object(name, src, allow_unproved = [], **kwargs):
    """Proves a Pia file and compiles it to an arm64 object file, `<name>.o`.

    piac refuses to compile a program with a failed or unproved goal, so the
    build fails unless every goal is proved, or accepted by one of
    `allow_unproved` (each passed as `--allow-unproved=<spec>`).

    Put the result in the `srcs` of a cc_library or cc_binary to call the
    program's functions from C (docs/codegen.md, "C ABI").
    """
    flags = " ".join(["--allow-unproved=" + spec for spec in allow_unproved])
    native.genrule(
        name = name,
        srcs = [src],
        outs = [name + ".o"],
        cmd = "$(location //tools/piac) --emit=obj %s -o $@ $<" % flags,
        tools = ["//tools/piac"],
        **kwargs
    )
