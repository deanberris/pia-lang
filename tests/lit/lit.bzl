"""One sh_test per test file, running its `// RUN:` lines (see run_lit.sh)."""

load("@rules_shell//shell:sh_test.bzl", "sh_test")

def lit_tests(name, srcs, tools = ["//tools/pia-opt"], data = []):
    """Declares `<file>_test` for each file in `srcs` and a suite `name`.

    Args:
      name: the test_suite's name.
      srcs: .mlir, .pia or literate .pia.md test files with `// RUN:` lines.
      tools: binaries the RUN lines call by name; FileCheck is always there.
      data: other files the RUN lines read, through `%S`.
    """
    all_tools = tools + ["@llvm-project//llvm:FileCheck"]
    tests = []
    for src in srcs:
        stem = src[:-len(".pia.md")] if src.endswith(".pia.md") else src.rsplit(".", 1)[0]
        test_name = stem + "_test"
        sh_test(
            name = test_name,
            srcs = ["//tests/lit:run_lit.sh"],
            args = ["$(rootpath %s)" % src] + ["$(rootpath %s)" % t for t in all_tools],
            data = [src] + all_tools + data,
        )
        tests.append(test_name)
    native.test_suite(name = name, tests = tests)
