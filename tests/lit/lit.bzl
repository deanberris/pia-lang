"""One sh_test per .mlir file, running its `// RUN:` lines (see run_lit.sh)."""

load("@rules_shell//shell:sh_test.bzl", "sh_test")

def mlir_lit_tests(name, srcs):
    tests = []
    for src in srcs:
        test_name = src.removesuffix(".mlir") + "_test"
        sh_test(
            name = test_name,
            srcs = ["//tests/lit:run_lit.sh"],
            args = [
                "$(rootpath //tools/pia-opt)",
                "$(rootpath @llvm-project//llvm:FileCheck)",
                "$(rootpath %s)" % src,
            ],
            data = [
                src,
                "//tools/pia-opt",
                "@llvm-project//llvm:FileCheck",
            ],
        )
        tests.append(test_name)
    native.test_suite(name = name, tests = tests)
