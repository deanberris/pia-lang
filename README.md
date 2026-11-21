# Pia

**Pia is a programming language whose compiler proves your code correct before it runs.**

Every integer overflow, every array index and every contract in a Pia program is a proof obligation. The compiler discharges them at compile time with interval analysis and the [Z3](https://github.com/Z3Prover/z3) SMT solver. When a proof fails, you get a compile error with a counterexample: concrete inputs that break your code. When every proof succeeds, the checks are gone from the machine code, because they can never fail.

The name is the second half of *Sophia*, and it stands for **Proved In Advance**.

[Documentation](https://pia-lang.dev/) · [Getting started](docs/getting-started.md) · [Demo](docs/demo.md) · [Stream delineation](docs/streams.pia.md) · [Language tour](docs/tour.md) · [How verification works](docs/verification.md) · [Status and roadmap](docs/status.md)

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
  counterexample: a = 255, b = 255, result = 510
average.pia:3:11: proved: the divisor is not zero [intervals]
average.pia:3:11: proved: '/' does not overflow u8 [intervals]
average.pia:2:3: proved: the postcondition holds [smt]
3 proved, 1 failed, 0 skipped
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
average_fixed.pia:3:23: proved: '+' does not overflow u16 [intervals]
average_fixed.pia:3:36: proved: the divisor is not zero [intervals]
average_fixed.pia:3:36: proved: '/' does not overflow u16 [intervals]
average_fixed.pia:3:3: proved: the value fits in u8 [smt]
average_fixed.pia:2:3: proved: the postcondition holds [smt]
5 proved, 0 failed, 0 skipped
```

Interval analysis settles the easy goals for free, and Z3 settles the rest. The counterexample is the input that breaks your code, so you know what to fix.

The proofs cost nothing at run time: a proved index has no bounds check and a proved sum has no overflow check. When arithmetic should clamp instead of failing, say so with `+|` or `@overflow(saturate)`, and the behaviour is defined, so there is nothing to prove. This loop adds two rows of pixels, and LLVM vectorises it into NEON saturating adds, 64 bytes per iteration:

<!-- example: add_rows.pia -->
```ocaml
let add_rows (a : [u8]) (b : [u8]) (dst : out mutable [u8]) : unit
  requires len a = len dst && len b = len dst
= for i in 0..len dst do dst.[i] <- a.[i] +| b.[i] done
```

```console
$ piac --emit=asm add_rows.pia
...
LBB0_10:
	ldp	q0, q1, [x10, #-32]
	ldp	q2, q3, [x10], #64
	ldp	q4, q5, [x12, #-32]
	ldp	q6, q7, [x12], #64
	uqadd.16b	v0, v0, v4
	uqadd.16b	v1, v1, v5
	uqadd.16b	v2, v2, v6
	uqadd.16b	v3, v3, v7
...
```

The bounds goals inside the loop are proved first: `i < len dst` from the loop's range, and the precondition gives the other two lengths. `piac` generates code only when every goal is proved.

## What is in Pia

- **Proved, not checked.** Overflow, bounds, division by zero, preconditions, postconditions, assertions and quantified properties (`forall`, `exists`) are all proved at compile time. The strongest guarantee is the default, and weaker behaviour such as wrapping arithmetic is opt-in and explicit.
- **An ML-style language.** One `let` for every definition, including types, which are values. Curried functions, records as values, and range types such as `int{0..255}`.
- **Metaprogramming from day one.** Operators are not built in: `+` is a metaprogram in the prelude that expands to `add`. Derives such as `@derive(eq)` generate code that is then type checked and proved like code you wrote.
- **Built on MLIR.** `piac` lowers Pia to its own MLIR dialects, proves the goals there, then compiles through LLVM to arm64 for Apple Silicon, with NEON vectorisation.
- **Editor support.** A language server shows failed proofs and their counterexamples as you type, and a VS Code extension uses it.

## Status

Pia is early and experimental. The compiler proves and compiles straight-line code, records, contracts and quantifiers today, and loops, cut at their invariants with termination checked by `decreases`, and compiles them (loops vectorised). Modules, generics, floats, variants and the concurrency model are designed but not built. [Status and roadmap](docs/status.md) has the details. The long-term target is a provably correct GIS pipeline, stream delineation and sediment transport over terrain images, running across the CPU and GPU.

## Building

Pia builds with [Bazel](https://bazel.build) through [Bazelisk](https://github.com/bazelbuild/bazelisk). The first build compiles the parts of LLVM and MLIR that Pia uses, so it takes a while.

```sh
bazel build //tools/piac //tools/pia-lsp
bazel test //...
```

See [Getting started](docs/getting-started.md) for the details, and [`editors/vscode`](editors/vscode/README.md) for the VS Code extension.

CI ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) runs `bazel build //...` and `bazel test //...` on a GitHub-hosted Apple Silicon macOS runner for every pull request and every push to `main`. A run saves the Bazel disk cache once per set of dependencies, so only the first run builds LLVM, MLIR and Z3. A run that fails or times out saves what it built under its own key, and a failed run uploads its test logs.

## Learn more

- [Language tour](docs/tour.md): the language as it is implemented today, with every example checked by the test suite
- [How verification works](docs/verification.md): goals, intervals, Z3 and counterexamples
- [Language design](docs/design.md): the whole language as designed, including the parts still to come
- [Compiler architecture](docs/architecture.md), [grammar](docs/grammar.md), [IRGen](docs/irgen.md), [verifier](docs/verifier.md), [codegen](docs/codegen.md) and [metaprograms](docs/meta.md)
- [Architecture Decision Records](docs/adr/README.md): why Pia is the way it is

Every example in this README and in the user documentation is a test: `bazel test //tests/docs:doc_examples_test` runs each one through `piac` and compares the output.

## License

Pia is licensed under the Apache License 2.0. See [LICENSE](LICENSE).
