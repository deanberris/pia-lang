"""Compiler flags for the codegen benchmarks (ADR 0075, section 3).

Every program of a problem is built for the same CPU as piac's output
(tools/piac/targets.bzl), at its compiler's highest optimisation level, with
no LTO and no PGO, since piac has neither. C and C++ do not contract a * b + c
into an FMA, because Pia does not unless the program licenses it (ADR 0012),
and clang does by default. Bazel's default C flags add a stack protector and
frame pointers, which piac's objects do not have, so they are turned off.
"""

C_OPTS = [
    "-O3",
    "-ffp-contract=off",
    "-fno-stack-protector",
    "-fomit-frame-pointer",
] + select({
    "//tools/piac:linux_x86_64": ["-march=x86-64-v3"],
    "//conditions:default": ["-mcpu=apple-m1"],
})

# piac's -O3, which runs LLVM's -O3 pipeline on the lowered module.
PIA_OPT_LEVEL = 3

RUST_OPTS = [
    "-Copt-level=3",
    "-Cdebuginfo=0",
] + select({
    "//tools/piac:linux_x86_64": ["-Ctarget-cpu=x86-64-v3"],
    "//conditions:default": ["-Ctarget-cpu=apple-m1"],
})

# The mode (ReleaseFast) is set by zig_configure_binary, not a flag.
ZIG_OPTS = select({
    "//tools/piac:linux_x86_64": ["-mcpu=x86_64_v3"],
    "//conditions:default": ["-mcpu=apple_m1"],
})
