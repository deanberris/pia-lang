# Pia

**Pia is a programming language whose compiler proves your code correct before it runs.**

Every integer overflow, every array index and every contract in a Pia program is a proof obligation. The compiler discharges them at compile time with interval analysis and the [Z3](https://github.com/Z3Prover/z3) SMT solver. When a proof fails, you get a compile error with a counterexample: concrete inputs that break your code. When every proof succeeds, the checks are gone from the machine code, because they can never fail.

The name is the second half of *Sophia*, and it stands for **Proved In Advance**.

[Documentation](https://deanberris.github.io/pia-lang/) · [Getting started](docs/getting-started.md) · [Language tour](docs/tour.md) · [How verification works](docs/verification.md) · [Status and roadmap](docs/status.md)

## A first proof

Here is the classic way to average two bytes:

<!-- example: average.pia -->
<!-- expect: fail -->
```ocaml
let average (a : u8) (b : u8) : u8
  ensures 2 * result <= a + b && a + b <= 2 * result + 1
= (a + b) / 2
```

The postcondition after `ensures` says what `average` means. In most languages this compiles, and it is wrong for large inputs, because `a + b` overflows a byte. Pia refuses it, and says why:

```console
$ piac --verify average.pia
average.pia:3:6: failed: '+' does not overflow u8
  counterexample: a = 128, b = 128, result = 256
...
```

The fix is to add in a wider type. Now every goal is proved, including the postcondition and the narrowing of the result back to `u8`:

<!-- example: average_fixed.pia -->
```ocaml
let average (a : u8) (b : u8) : u8
  ensures 2 * result <= a + b && a + b <= 2 * result + 1
= let total : u16 = a + b in total / 2
```

```console
$ piac --verify average_fixed.pia
...
```

The proofs cost nothing at run time. When the arithmetic should clamp instead, say so, and the proof obligation goes away because the behaviour is defined. This compiles to a single NEON instruction:

<!-- example: add_px.pia -->
```ocaml
let add_px (a : u8) (b : u8) : u8 @overflow(saturate) = a + b
```

```console
$ piac --emit=asm add_px.pia
...
_add_px:
...
	uqadd	b0, b0, b1
...
```

## What is in Pia

- **Proved, not checked.** Overflow, bounds, division by zero, preconditions, postconditions, assertions and quantified properties (`forall`, `exists`) are all proved at compile time. The strongest guarantee is the default, and weaker behaviour such as wrapping arithmetic is opt-in and explicit.
- **An ML-style language.** One `let` for every definition, including types, which are values. Curried functions, records as values, and range types such as `int{0..255}`.
- **Metaprogramming from day one.** Operators are not built in: `+` is a metaprogram in the prelude that expands to `add`. Derives such as `@derive(eq)` generate code that is then type checked and proved like code you wrote.
- **Built on MLIR.** `piac` lowers Pia to its own MLIR dialects, proves the goals there, then compiles through LLVM to arm64 for Apple Silicon, with NEON vectorisation.
- **Editor support.** A language server shows failed proofs and their counterexamples as you type, and a VS Code extension uses it.

## Status

Pia is early and experimental. The compiler proves and compiles straight-line code, records, contracts and quantifiers today, and compiles loops (vectorised), but it does not prove the goals inside loops yet. Modules, generics, floats, variants and the concurrency model are designed but not built. [Status and roadmap](docs/status.md) has the details. The long-term target is a provably correct GIS pipeline, stream delineation and sediment transport over terrain images, running across the CPU and GPU.

## Building

Pia builds with [Bazel](https://bazel.build) through [Bazelisk](https://github.com/bazelbuild/bazelisk). The first build compiles the parts of LLVM and MLIR that Pia uses, so it takes a while.

```sh
bazel build //tools/piac //tools/pia-lsp
bazel test //...
```

See [Getting started](docs/getting-started.md) for the details, and [`editors/vscode`](editors/vscode/README.md) for the VS Code extension.

## Learn more

- [Language tour](docs/tour.md): the language as it is implemented today, with every example checked by the test suite
- [How verification works](docs/verification.md): goals, intervals, Z3 and counterexamples
- [Language design](docs/design.md): the whole language as designed, including the parts still to come
- [Compiler architecture](docs/architecture.md), [grammar](docs/grammar.md), [IRGen](docs/irgen.md), [verifier](docs/verifier.md), [codegen](docs/codegen.md) and [metaprograms](docs/meta.md)
- [Architecture Decision Records](docs/adr/README.md): why Pia is the way it is

Every example in this README and in the user documentation is a test: `bazel test //tests/docs:doc_examples_test` runs each one through `piac` and compares the output.

## License

Pia is licensed under the Apache License 2.0. See [LICENSE](LICENSE).
