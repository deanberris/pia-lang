# How verification works

`piac` does not compile a program until it has proved it. This page explains what it proves, how, and how to read its reports. The [verifier notes](verifier.md) have the details of the encoding.

## Goals

A *goal* is a fact the compiler must establish. Some come from your contracts, and the rest come from the code itself:

| Goal | Raised by |
| --- | --- |
| no overflow | `+ - * /` in the default `@overflow(proof)` mode, and every narrowing conversion |
| nonzero divisor | every `/`, `%` and `mod` |
| in bounds | every `xs.[i]`, read or written |
| precondition | every call, for each of the callee's `requires` |
| postcondition | every return, for each `ensures` |
| assertion | every `assert` |
| loop invariant and measure | each loop's `invariant` and `decreases` |

`piac --verify` prints one line per goal, in program order, then a summary. This function raises three goals, one for each operation:

<!-- example: scale.pia -->
```ocaml
let scale (xs : [u16]) (i : usize) (k : u16) : u32
  requires i < len xs
= xs.[i] * k / 2
```

```console
$ piac --verify scale.pia
scale.pia:3:3: proved: the index is within bounds [smt]
scale.pia:3:10: proved: '*' does not overflow u32 [intervals]
scale.pia:3:14: proved: the divisor is not zero [intervals]
scale.pia:3:14: proved: '/' does not overflow u32 [intervals]
4 proved, 0 failed, 0 skipped
```

Every line has the source location, the claim, and the method that settled it. A goal is **proved**, **failed** (with a counterexample when the solver has one), or **skipped** when this version of the verifier cannot decide it yet.

## Intervals first, then Z3

Most goals are easy, and the verifier settles those without a solver. Each value has a range: its type, narrowed by constants, widening conversions and arithmetic. If `a : u8` and `b : u8`, then `a + b` lies in `[0, 510]`, so it fits in a `u16`. A goal proved this way is marked `[intervals]`:

<!-- example: mac.pia -->
```ocaml
let mac (a : u8) (b : u8) (c : u16) : u32 = a * b + c
```

```console
$ piac --verify mac.pia
mac.pia:1:47: proved: '*' does not overflow u32 [intervals]
mac.pia:1:51: proved: '+' does not overflow u32 [intervals]
2 proved, 0 failed, 0 skipped
```

Everything else goes to Z3. Each remaining goal becomes one query: the function's parameters with their types' ranges, its preconditions, the operations up to the goal, the goals before it (each is proved in its own query, so this is sound), and the *negation* of the goal. If Z3 finds that query unsatisfiable, no input can break the goal, and it is proved. If Z3 finds a model, the model is an input that breaks it: the counterexample.

The query is built in MLIR's `smt` dialect, exported to SMT-LIB and solved by Z3 inside the compiler. `piac --dump-smt` prints each one.

## Reading a counterexample

A counterexample names the function's parameters, using `p.r` for a field of a record and `len xs` for the length of a slice. For an overflow it adds the exact `result` that did not fit, and for an index the `index` and `length`.

<!-- example: bounds.pia -->
<!-- expect: fail -->
```ocaml
let second (xs : [u8]) : u8 = xs.[1]
```

```console
$ piac --verify bounds.pia
bounds.pia:1:31: failed: the index is within bounds
  counterexample: len xs = 0, index = 1, length = 0
0 proved, 1 failed, 0 skipped
```

An empty slice breaks the index, and so would any slice shorter than two elements. The fix is to say what the function needs, which moves the obligation to every caller:

```ocaml
let second (xs : [u8]) : u8
  requires len xs >= 2
= xs.[1]
```

## Contracts are the interface

When one function calls another, the verifier does not look inside the callee. It proves the callee's preconditions with the arguments substituted, then assumes its postconditions about the result. So each function is proved once, on its own, and a call is only as strong as the contract it calls.

<!-- example: calls.pia -->
<!-- expect: fail -->
```ocaml
let inc (x : u8) : u8
  requires x < 255
  ensures result = x + 1
= x + 1

let twice (x : u8) : u8 = inc (inc x)
```

```console
$ piac --verify calls.pia
calls.pia:4:5: proved: '+' does not overflow u8 [smt]
calls.pia:3:3: proved: the postcondition holds [smt]
calls.pia:6:32: failed: the precondition of 'inc' holds
  counterexample: x = 255
calls.pia:6:27: failed: the precondition of 'inc' holds
  counterexample: x = 254
2 proved, 2 failed, 0 skipped
```

Both calls fail: the inner one when `x` is 255, and the outer one when `x` is 254, because the inner call then returns 255. Adding `requires x < 200` to `twice` proves both. This is the same assume-guarantee rule that modules will use across files, where a module is proved against the interfaces it imports and never against another module's code.

## What it means for code generation

Codegen runs only when no goal has failed. It erases every contract and everything only contracts used, such as quantifiers and `old`. A proved index needs no bounds check and a proved addition needs no overflow check, so the machine code has none. Proved facts are also what lets LLVM vectorise loops safely.

Skipped goals are not failures, so `piac` compiles the program, but it warns that they were not proved. Today that means goals inside loops; see [Status](status.md).

## Where it goes next

- **Loops.** The verifier will cut each loop at its invariant: prove it on entry and after each iteration, assume it at the head, and forget only what the loop assigns. Then the goals inside loops will be proved, and the warning goes away.
- **Presburger arithmetic for affine goals.** Subscripts such as `xs.[2*i + 1]`, aliasing between buffers and loop-carried dependence are linear integer problems. MLIR's Presburger library will decide them between intervals and Z3 ([ADR 0020](adr/0020-presburger-for-affine-goals.md)).
- **Termination.** `decreases` measures will be proved.
- **Modules and proof certificates.** Each compiled module will carry a certificate naming the hashes of the interfaces it was proved against, and the linker will refuse a stale one ([ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md)).
