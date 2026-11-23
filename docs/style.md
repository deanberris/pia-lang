# Style guide

This page says how code in the Pia repository is written: the C++ compiler and tools, the Python test and build scripts, the Bazel files, and the documentation. Pia code itself has its own page, [Idiomatic Pia](idioms.md), and the lints that go with it ([ADR 0037](adr/0037-idiomatic-pia-and-lints.md)). This page does not repeat them.

The rules are here so that a reader, whether a person or an agent, can find their way around any file in the same way. Two of them apply to every language in the repository and matter more than the rest.

## Return early

Handle the special cases first and return, so the main path of a function reads straight down at one level of indentation. Do not nest the main path inside a chain of `if` statements.

Instead of this:

```cpp
std::optional<Interval> rangeOf(const Node &type) {
  if (type.kind == NodeKind::RangeType) {
    if (type.kids.size() == 2) {
      auto lo = constant(*type.kids[0]);
      auto hi = constant(*type.kids[1]);
      if (lo && hi) {
        return Interval{*lo, *hi};
      }
    }
  }
  return std::nullopt;
}
```

write this:

```cpp
std::optional<Interval> rangeOf(const Node &type) {
  if (type.kind != NodeKind::RangeType || type.kids.size() != 2)
    return std::nullopt;
  auto lo = constant(*type.kids[0]);
  auto hi = constant(*type.kids[1]);
  if (!lo || !hi)
    return std::nullopt;
  return Interval{*lo, *hi};
}
```

The same goes for loops: use `continue` to skip the elements a loop does not care about, rather than wrapping its body in an `if`. Do not write `else` after a `return`, `break` or `continue`. When a function needs more than two or three levels of nesting, split part of it into a helper with a name that says what it does.

This is the [LLVM rule](https://llvm.org/docs/CodingStandards.html#use-early-exits-and-continue-to-simplify-code) too, and `clang-tidy` checks the `else` part of it (`readability-else-after-return`).

## Comments say why

The code already says what it does. A comment is for what the code cannot say: why it is written this way, what would go wrong if it were written the obvious way, which invariant it relies on, which ADR or issue decided it, and what a measurement showed.

Do not write comments like these, which repeat the code:

```cpp
// Increment the counter.
++count;

// Loop over the goals.
for (const Goal &g : goals) {
```

Write comments like these, which tell the reader something the code cannot:

```cpp
// Interval analysis runs first because it settles most bounds goals without
// calling the solver; only what it cannot decide goes to Z3 (ADR 0020).
if (auto r = intervals.decide(goal))
  return *r;

// Lints read the syntax tree before metaprograms expand, so a warning points
// at text the user wrote rather than at generated code.
```

Some more guidance:

- **A header starts with a comment that says what it is for**, and where its design is written down. See [`src/syntax/Lint.h`](../src/syntax/Lint.h) for an example. A `.cpp` file that implements one header needs no comment of its own; one that stands alone, such as a tool's `main`, gets one.
- **A declaration in a header gets a comment** saying what it promises its callers: what it returns, what it requires, and what it does when something goes wrong. That is the contract, and it is not obvious from the signature.
- **Link to the decision.** When code is the way it is because of an ADR, an issue or a measured result, name it: `(ADR 0026)`, `(#152)`. The reasoning lives there, and the comment stays short.
- **Keep comments true.** A comment that no longer matches the code is worse than none. When you change code, read the comments around it.
- **Do not leave code commented out.** Git remembers it.
- **TODOs name an issue:** `// TODO(#153): open-sided ranges.` A TODO without an issue tends to stay forever.

## C++

The compiler, the language server and the tools follow the [LLVM Coding Standards](https://llvm.org/docs/CodingStandards.html). Read them once; most of what follows is a reminder of the parts that come up most, and of the few places where Pia adds to them.

The language is C++17 (`.bazelrc`).

### Formatting

Formatting is whatever `clang-format` produces with the repository's [`.clang-format`](https://github.com/deanberris/pia-lang/blob/main/.clang-format), which is LLVM style: two-space indentation, 80 columns, and `&` and `*` next to the name (`const Node &n`).

```console
$ pip install clang-format==18.1.8
$ git clang-format origin/main
```

The first line installs the same `clang-format` that CI uses, since versions differ in small ways. The second formats only the lines your branch changed since `main`. Format what you touch, and do not reformat whole files in a change that is about something else: it buries the real change in the diff and conflicts with other work in flight. A pull request that only reformats is welcome when nobody else is working in that file.

A table laid out by hand, such as the X-macro list of token kinds in [`src/syntax/Token.h`](../src/syntax/Token.h), goes between `// clang-format off` and `// clang-format on`, with a comment saying why. clang-format would otherwise reflow it, and not always the same way twice.

CI checks the lines a pull request changes with `git clang-format --diff` ([`.github/workflows/style.yml`](https://github.com/deanberris/pia-lang/blob/main/.github/workflows/style.yml)). Lines you did not touch are not checked.

### Naming

Pia's C++ uses the names [MLIR uses](https://mlir.llvm.org/getting_started/DeveloperGuide/#style-guide), which is the LLVM standard with lower-case variables:

| What | Style | Example |
| --- | --- | --- |
| types, classes, structs, enums | `UpperCamelCase` | `TextEdit`, `NodeKind` |
| functions and methods | `lowerCamelCase`, a verb | `lint`, `printLint`, `rangeOf` |
| variables, parameters, fields | `lowerCamelCase`, a noun | `fixTitle`, `source` |
| enumerators | `UpperCamelCase` | `NodeKind::RangeType` |
| namespaces | lower case | `pia::syntax` |
| private data members of a class | `lowerCamelCase_`, with a trailing underscore | `diags_`, `pos_` |
| macros | `UPPER_CASE` | `PIA_SYNTAX_LINT_H` |

The code is built on MLIR and calls its APIs everywhere, so following MLIR keeps one style across the boundary. The trailing underscore is Pia's own addition, used throughout `src/`: it tells a member from a local at a glance in long methods. Public fields of a plain `struct` have no underscore. Short names (`n`, `os`, `loc`) are fine for a value whose scope is a few lines. Longer scopes get longer names.

### Files and headers

- Source files are `.cpp` and headers are `.h`, named after the main thing they define (`Lint.h`, `Verifier.cpp`).
- Header guards are `PIA_<DIRECTORY>_<FILE>_H`, such as `PIA_SYNTAX_LINT_H`.
- Include what you use, and nothing more. Includes are ordered as LLVM orders them: the file's own header first, then Pia's headers, then LLVM and MLIR, then the C++ standard library, each group sorted. `clang-format` sorts within a group.
- Do not put `using namespace` in a header.
- Give helpers that are private to a `.cpp` file internal linkage: `static` for functions, an anonymous namespace for types.

### Code

- **Early returns and `continue`**, as [above](#return-early).
- **`auto`** where the type is obvious from the right-hand side or does not help the reader (iterators, `dyn_cast` results). Spell the type out otherwise.
- **Errors** in the compiler are diagnostics, reported against a source location, with a message that says what went wrong in the user's terms. Do not `abort` or `assert` on bad user input; `assert` is for things that cannot happen if the compiler is correct, and its message says what was expected.
- **Prefer LLVM's and MLIR's containers and utilities** where the surrounding code uses them (`SmallVector`, `StringRef`, `llvm::any_of`), and the standard library where it does not. Code in `src/syntax` does not link LLVM, so that `pia-lsp` can share it, and uses the standard library only.
- **No RTTI**, as in LLVM: use `isa`, `cast` and `dyn_cast` rather than `dynamic_cast`.
- **Errors are values**: `std::optional`, `llvm::Expected`, `mlir::LogicalResult` or `FailureOr`. Do not add new exceptions. The parser and the metaprogram interpreter throw internally to unwind to a recovery point, and catch before anything crosses their public API; keep it that way.
- **Keep functions short.** A function that does not fit on a screen usually hides two or three smaller ones with names worth reading.

### clang-tidy

The repository's [`.clang-tidy`](https://github.com/deanberris/pia-lang/blob/main/.clang-tidy) turns on a small set of checks that match the rules on this page, including `readability-else-after-return`, `readability-identifier-naming` and LLVM's own checks. Editors that use `clangd` pick it up. It is advice for now: CI does not run it, because it needs the whole build's compile commands.

## Python

Python in `tests/` and `tools/` follows [PEP 8](https://peps.python.org/pep-0008/) with four-space indentation. Scripts use only the standard library unless a `requirements.txt` next to them says otherwise, and start with a docstring that says what the script is for and how to run it. Return early and comment why here too.

## Bazel

`BUILD.bazel` and `.bzl` files are formatted by [buildifier](https://github.com/bazelbuild/buildtools/blob/main/buildifier/README.md). Targets in a file are listed in the order a reader needs them, usually the library first and its tests after.

## Documentation

- Write in plain, full sentences, in British spelling, as the existing pages do.
- **Every example is a test.** Each `ocaml` block in the user documentation goes through `piac --verify`, and each `console` block that starts with `$ piac` must match the real output (`bazel test //tests/docs:doc_examples_test`). Paste output from a real run. Do not edit it by hand.
- A change to how the language works starts as a design note or an [ADR](adr/README.md), so the reasoning is written before the code.
- The site must build with `mkdocs build --strict`.
