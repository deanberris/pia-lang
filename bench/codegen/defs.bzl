"""The Bazel macro for one codegen benchmark problem (ADR 0075, section 3)."""

load("@rules_cc//cc:defs.bzl", "cc_binary")
load("@rules_rust//rust:defs.bzl", "rust_binary")
load("@rules_shell//shell:sh_test.bzl", "sh_test")
load("@rules_zig//zig:defs.bzl", "zig_binary", "zig_configure_binary")
load("//tools/piac:pia.bzl", "pia_object")
load("//tools/piac:targets.bzl", "PIA_TARGETS")
load(":flags.bzl", "C_OPTS", "PIA_OPT_LEVEL", "RUST_OPTS", "ZIG_OPTS")

def codegen_benchmark(
        name,
        pia,
        driver,
        check_args,
        expected,
        control = None,
        c = None,
        cpp = None,
        rust = None,
        zig = None):
    """Builds every program of one problem and tests that they agree.

    Makes `<name>_pia` (the Pia port, linked with its C `driver`),
    `<name>_control` (the Pia program transcribed into C, when the proof made
    the port differ from the reference), and one binary for each reference
    given: `<name>_c`, `<name>_cpp`, `<name>_rust` and `<name>_zig`.
    `<name>_test` runs each with `check_args` and checks that it prints
    `expected`. tools/bench/codegen_bench.py runs the same binaries on the
    benchmark input.
    """
    pia_object(
        name = name + "_pia_obj",
        src = pia,
        opt_level = PIA_OPT_LEVEL,
        target_compatible_with = PIA_TARGETS,
    )
    cc_binary(
        name = name + "_pia",
        srcs = [driver, ":" + name + "_pia_obj"],
        copts = C_OPTS,
        target_compatible_with = PIA_TARGETS,
    )
    programs = [":" + name + "_pia"]
    if control:
        cc_binary(name = name + "_control", srcs = [control], copts = C_OPTS)
        programs.append(":" + name + "_control")
    if c:
        cc_binary(name = name + "_c", srcs = [c], copts = C_OPTS)
        programs.append(":" + name + "_c")
    if cpp:
        cc_binary(name = name + "_cpp", srcs = [cpp], copts = C_OPTS + ["-std=c++20"])
        programs.append(":" + name + "_cpp")
    if rust:
        rust_binary(
            name = name + "_rust",
            srcs = [rust],
            crate_root = rust,
            edition = "2021",
            rustc_flags = RUST_OPTS,
        )
        programs.append(":" + name + "_rust")
    if zig:
        zig_binary(
            name = name + "_zig_debug",
            main = zig,
            zigopts = ZIG_OPTS,
            tags = ["manual"],
        )
        zig_configure_binary(
            name = name + "_zig",
            actual = ":" + name + "_zig_debug",
            mode = "release_fast",
        )
        programs.append(":" + name + "_zig")
    sh_test(
        name = name + "_test",
        srcs = ["//bench/codegen:same_output_test.sh"],
        args = [expected, " ".join(check_args)] + ["$(rootpath %s)" % p for p in programs],
        data = programs,
        target_compatible_with = PIA_TARGETS,
    )
