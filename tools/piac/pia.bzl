"""Bazel rules for compiling Pia programs with piac."""

def pia_object(
        name,
        src,
        allow_unproved = [],
        solver_rlimit = 1200000000,
        solver_timeout_ms = 600000,
        **kwargs):
    """Proves a Pia file and compiles it to an arm64 object file, `<name>.o`.

    piac refuses to compile a program with a failed or unproved goal, so the
    build fails unless every goal is proved, or accepted by one of
    `allow_unproved` (each passed as `--allow-unproved=<spec>`).

    Each obligation gets `solver_rlimit` units of Z3's deterministic resource
    limit (`--solver-rlimit`). The rlimit, not the wall clock, decides whether
    a goal is proved, so the result does not depend on how loaded the machine
    is. The default is about 20 times the costliest goal in the repository,
    as measured by `piac --solver-cost` (docs/verifier.md, "Timeouts").

    `solver_timeout_ms` is only a last-resort safety net against a query
    that runs for a long time without spending its rlimit; it should never
    be what decides a goal.

    Put the result in the `srcs` of a cc_library or cc_binary to call the
    program's functions from C (docs/codegen.md, "C ABI").
    """
    flags = " ".join(["--allow-unproved=" + spec for spec in allow_unproved] +
                     ["--solver-rlimit=%d" % solver_rlimit,
                      "--solver-timeout=%d" % solver_timeout_ms])
    native.genrule(
        name = name,
        srcs = [src],
        outs = [name + ".o"],
        cmd = "$(location //tools/piac) --emit=obj %s -o $@ $<" % flags,
        tools = ["//tools/piac"],
        **kwargs
    )
