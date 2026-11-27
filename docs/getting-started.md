# Getting started

This page builds `piac`, proves a first program, compiles it, and sets up VS Code.

## Requirements

- **Bazelisk.** Pia builds with Bazel, at the version in `.bazelversion`. [Bazelisk](https://github.com/bazelbuild/bazelisk) reads that file and fetches the right Bazel. On macOS, `brew install bazelisk`.
- **A C++17 compiler.** On macOS, Xcode or its command line tools. On Linux, Clang or GCC.
- **Network access** to the Bazel Central Registry and GitHub for the first build, which fetches LLVM, MLIR and Z3.

Pia is developed on Apple silicon Macs, and builds, proves, compiles and runs on Linux x86_64 too ([ADR 0049](adr/0049-targets-are-theories.md)).

## Build

```sh
git clone https://github.com/deanberris/pia-lang.git
cd pia-lang
bazel build //tools/piac //tools/pia-lsp
```

The first build compiles the parts of LLVM and MLIR that Pia uses, which takes 15 minutes or more. Later builds reuse the disk cache in `~/.cache/pia-bazel-disk`, including after `bazel clean`.

The compiler is now at `bazel-bin/tools/piac/piac`. The examples below call it `piac`, so put it on your `PATH` or make an alias:

```sh
alias piac="$PWD/bazel-bin/tools/piac/piac"
```

Run the tests with:

```sh
bazel test //...
```

## Prove a program

Save this as `clamp.pia`:

<!-- example: clamp.pia -->
```ocaml
let clamp (lo : i32) (hi : i32) (x : i32) : i32
  requires lo <= hi
  ensures lo <= result && result <= hi
  ensures lo <= x && x <= hi ==> result = x
= if x < lo then lo else if x > hi then hi else x
```

`requires` is a precondition: callers must prove it, and the body may assume it. `ensures` is a postcondition, where `result` is the value returned. Ask `piac` to prove it:

```console
$ piac --verify clamp.pia
clamp.pia:3:3: proved: the postcondition holds [smt]
clamp.pia:4:3: proved: the postcondition holds [smt]
2 proved, 0 failed, 0 skipped
```

Each line is one *goal*, a fact the compiler had to establish, with its source location and how it was proved: `intervals` for the cheap range analysis, `smt` for Z3. The exit status is 0 when nothing failed.

Now break it. Change the postcondition to the wrong claim `ensures lo < result`, and `piac` shows inputs where it is false:

<!-- example: clamp_bad.pia -->
<!-- expect: fail -->
```ocaml
let clamp (lo : i32) (hi : i32) (x : i32) : i32
  requires lo <= hi
  ensures lo < result
= if x < lo then lo else if x > hi then hi else x
```

```console
$ piac --verify clamp_bad.pia
clamp_bad.pia:3:3: failed: the postcondition holds
  counterexample: lo = 1028093, hi = 2147483647, x = 0
0 proved, 1 failed, 0 skipped
```

The counterexample is an input that breaks the claim. Here `x` is below `lo`, so `clamp` returns `lo`, and `lo < lo` is false. Z3 picks whichever values it finds first, so they can look arbitrary, but they always break the goal.

## Compile a program

`piac --emit=obj` proves the program, then compiles it to an object file for the machine it runs on. Code is generated only when no goal fails.

A file is a module, and everything in it is private unless an interface the module claims lists it ([ADR 0039](adr/0039-module-and-interface-syntax.md)). A file with no `module` header exports nothing. To call `clamp` from C, give the file a header and list `clamp` in an interface marked `@abi(c)`, which keeps C names:

<!-- example: clamp_c.pia -->
```ocaml
module Clamp : Clamping

interface Clamping @abi(c) = sig
  let clamp : (lo : i32) -> (hi : i32) -> (x : i32) -> i32
    requires lo <= hi
    ensures lo <= result && result <= hi
end

let clamp (lo : i32) (hi : i32) (x : i32) : i32
  requires lo <= hi
  ensures lo <= result && result <= hi
  ensures lo <= x && x <= hi ==> result = x
= if x < lo then lo else if x > hi then hi else x
```

The interface can promise less than the function proves: here it leaves out the last postcondition, and the compiler proves that what the function ensures implies what the interface says.

```sh
piac --emit=obj -o clamp.o clamp_c.pia
```

Each exported function becomes a C function. A C declaration for `clamp` is:

```c
#include <stdint.h>
int32_t clamp(int32_t lo, int32_t hi, int32_t x);
```

```sh
cc main.c clamp.o -o main
```

The [C ABI](codegen.md#c-abi) section of the codegen notes says how slices, arrays and records are passed. Other outputs stop earlier in the pipeline: `--emit=mlir` prints the Pia dialects, `--emit=core` the core MLIR dialects, `--emit=llvm` the LLVM IR and `--emit=asm` the assembly.

## Use another module

Another file reaches `clamp` by importing the interface that lists it. The importer is built against the interface alone, as an *interface artifact*, which `piac --emit=interface` writes, one file per interface (here `Clamp.Clamping.piai`):

```console
$ piac --emit=interface -o . clamp_c.pia
```

`import Clamp.Clamping` finds that file on the interface path, which `--iface-path` gives, and the module's items are then `Clamp.clamp`:

<!-- example: fit.pia -->
<!-- flags: --iface-path=. -->
```ocaml
import Clamp.Clamping

let fit (lo : i32) (hi : i32) (x : i32) : i32
  requires lo <= hi
  ensures lo <= result
= Clamp.clamp lo hi x
```

```console
$ piac --verify --iface-path=. fit.pia
fit.pia:6:3: proved: the precondition of 'Clamp.clamp' holds [smt]
fit.pia:5:3: proved: the postcondition holds [smt]
2 proved, 0 failed, 0 skipped
```

The call is checked against the interface's contract, never against the body of `clamp`: `fit` proves the precondition `lo <= hi` from its own, and its postcondition follows from what the interface ensures. The artifact holds only the interface, without comments, private items or bodies, so changing any of those leaves it byte-for-byte the same, and nothing that imports it is rebuilt. To link, compile both files to objects and pass both to the linker. In Bazel, the `pia_library` rule in `//tools/piac:pia.bzl` does all of this, and each module sees only the interfaces of the modules it lists in `deps` ([ADR 0039](adr/0039-module-and-interface-syntax.md)).

## piac at a glance

| Command | What it does |
| --- | --- |
| `piac --verify f.pia` | prove every goal and print a report |
| `piac --emit=obj -o f.o f.pia` | prove, then compile to an object file |
| `piac --emit=asm f.pia` | prove, then print assembly (also `llvm`, `core`) |
| `piac --emit=obj --report=f.goals -o f.o f.pia` | the same, also writing the goal report `--verify` prints to `f.goals`; `pia_library` keeps it as `<name>.goals`, so a test can check what the build proved without proving it again |
| `piac --emit=interface -o dir f.pia` | write the module's interface artifacts to `dir` |
| `piac --verify --iface-path=dir f.pia` | prove a program that imports interfaces found in `dir` |
| `piac --emit=mlir f.pia` | print the program in Pia's MLIR dialects |
| `piac --verify --emit=mlir f.pia` | both, with each proved op marked `pia.proved` |
| `piac --dump-smt f.pia` | print each SMT query sent to Z3 |
| `piac --dump-tokens f.pia` | print the token stream |
| `piac --dump-ast f.pia` | print the syntax tree |
| `piac --dump-expanded f.pia` | print the syntax tree after metaprograms run |
| `piac --check f.pia` | parse only |
| `piac --check --fragment=contracts f.pia` | parse a file of contract clauses alone |

`--target=<triple>` and `--cpu=<name>` choose the machine (`arm64-apple-macosx14.0.0` with `apple-m1`, or `x86_64-unknown-linux-gnu` with `x86-64-v3`; the default is the host), and `-O0` to `-O3` the optimisation level (default `-O2`). `--meta-cycles=N` caps metaprogram expansion (default 32).

The exit status is 0 on success, 1 when the program has an error or a goal fails, and 2 for a usage error.

## VS Code

The VS Code extension in [`editors/vscode`](https://github.com/deanberris/pia-lang/tree/main/editors/vscode) runs `pia-lsp`, Pia's language server. It shows failed goals with their counterexamples as errors in the editor, the proofs of each expression on hover, syntax errors as you type, go to definition, an outline and completion.

```sh
bazel build //tools/pia-lsp
cd editors/vscode
npm install
npx vsce package
code --install-extension pia-0.1.0.vsix
```

Then point the extension at the server in VS Code's settings:

```json
"pia.server.path": "/path/to/pia-lang/bazel-bin/tools/pia-lsp/pia-lsp"
```

By default it verifies when you save. Set `"pia.verify.on": "change"` to verify as you type. The [extension's README](https://github.com/deanberris/pia-lang/blob/main/editors/vscode/README.md) lists the settings and how to use `pia-lsp` from Neovim, Helix, Emacs, Zed or Sublime Text.

## Next

- [Language tour](tour.md): what you can write today
- [How verification works](verification.md): what the goals are and how they are proved
