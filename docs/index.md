# Pia: Proved In Advance

**Pia is a programming language whose compiler proves your code correct before it runs.**

Every integer overflow, every array index and every contract in a Pia program is a proof obligation. The compiler discharges them at compile time, with interval analysis and the [Z3](https://github.com/Z3Prover/z3) SMT solver. When a proof fails, you get a compile error with a counterexample. When every proof succeeds, the checks are gone from the machine code, because they can never fail.

## A first proof

<!-- example: average.pia -->
<!-- expect: fail -->
```ocaml
let average (a : u8) (b : u8) : u8
  ensures 2 * result <= a + b && a + b <= 2 * result + 1
= (a + b) / 2
```

This is the classic way to average two bytes, and it is wrong for large inputs, because `a + b` overflows a byte. Pia refuses it, and says why:

```console
$ piac --verify average.pia
average.pia:3:6: failed: '+' does not overflow u8
  counterexample: a = 255, b = 255, result = 510
average.pia:3:11: proved: the divisor is not zero [intervals]
average.pia:3:11: proved: '/' does not overflow u8 [intervals]
average.pia:2:3: proved: the postcondition holds [smt]
3 proved, 1 failed, 0 skipped
```

Add in a wider type, and every goal is proved, including the postcondition:

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

## What is in Pia

- **Proved, not checked.** Overflow, bounds, division by zero, preconditions, postconditions, assertions and quantified properties are all proved at compile time. The strongest guarantee is the default, and weaker behaviour, such as wrapping arithmetic, is explicit.
- **An ML-style language.** One `let` for every definition, including types, which are values. Records as values, range types such as `int{0..255}`, and parameters that state their ownership and access.
- **Metaprogramming from day one.** Operators are metaprograms in the prelude, and derives such as `@derive(eq)` generate code that is then proved like code you wrote.
- **Built on MLIR.** `piac` proves goals in its own MLIR dialects, then compiles through LLVM to arm64 for Apple Silicon, with NEON vectorisation.
- **Proofs in your editor.** A language server shows failed goals and their counterexamples as you work, in VS Code or any LSP editor.

## Where to go next

- [Getting started](getting-started.md): build `piac`, prove a program, set up VS Code
- [Demo: edge detection](demo.md): a real program built with Pia, and a bug the compiler catches
- [A tour of Pia](tour.md): the language as it is today, every example tested
- [How verification works](verification.md): goals, intervals, Z3 and counterexamples
- [Status and roadmap](status.md): what works, what does not yet, and what is next
- [Language design](design.md): the whole language as designed
- [Architecture Decision Records](adr/README.md): why Pia is the way it is

Pia is open source under the Apache License 2.0, at [github.com/deanberris/pia-lang](https://github.com/deanberris/pia-lang).
