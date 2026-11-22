# 37. Idiomatic Pia: facts in types first, written as opinions and checked by lints

Date: 2026-11-22

Status: Accepted

## Context

Dean asked what the difference is between a function with `requires x <= 100` on an integer parameter and one whose parameter is a range type, whether the compiler should say which one is checked by types and which by the prover, and whether it should push code towards types. He then asked for more of the same: anti-patterns that people can write, the better form of each, a philosophical hierarchy of how to say things in Pia, given as opinions rather than rules, and lints that point out where a metaprogram, a concept or a decomposed proof would be better, so that idiomatic Pia is defined early and the checkers do not take forever.

For one value checked against constants, a precondition and a range type say the same thing. What differs is where the fact lives, and what it costs. Measured on the iMac with `piac --verify --solver-cost`:

- **A precondition never uses intervals.** `f (y / 3)` for `requires x < 100` sends `the precondition of 'f' holds` to Z3, and so does a call whose argument is already `int{0..50}`. With `(x : int{0..99})`, an `int{0..50}` argument widens with no goal, and a wider one raises one narrowing goal, as before.
- **Inside the function, a range type turns solver goals into interval goals.** `x + 1` under `requires x < 100` is `[smt]`; with `x : int{0..99}` it is `[intervals]`.
- **A fact in a contract stops at the function.** With `requires forall (k in 0..len xs). xs.[k] < 16`, a caller's `t.[get xs i]` into a 16-entry table fails, because `get`'s `u8` result does not keep the bound; the file costs 10,022 resource units. With `xs : [int{0..15}]` and an `int{0..15}` result, the same index is proved by intervals and the file costs 96.
- **Nonlinear preconditions are expensive.** `requires w * h <= 1000000` on `u32` costs 1,075,117 units for one overflow goal (87 ms); with `int{0..1000}` parameters it is proved by intervals at cost 0.
- **`inc`/`twice` with constant preconditions** is 5 solver goals at cost 1,261; with range types, 4 goals, one by intervals, at cost 711.

Two measurements show where range types are not yet free:

- **Arithmetic with nothing wider expected happens at the range.** With `x : int{1..64}`, `let d = x - 1 in d` fails at `x = 1` (`'-' does not overflow int{1..64}`), while `x - 1` as a `u8` result is proved by intervals. IRGen computes arithmetic at the join of the operand types and the expected type, and an unannotated `let` expects nothing.
- **A literal takes the range's type.** `x + 200` with `x : int{0..99}` is rejected, `200 does not fit in int{0..99}`, even in an `@overflow(wrap)` function returning `u8`.

## Decision

### An "Idiomatic Pia" page of opinions

[docs/idioms.md](../idioms.md) gives the house opinions, as a hierarchy to prefer from the top:

1. Make illegal states unrepresentable with types: range types, element ranges on slices, variants instead of integer tags, slices instead of a buffer and a length, buffers of records instead of parallel arrays, and later record `where` invariants and refinement types.
2. Contracts for facts that relate several values.
3. Spec functions and lemmas, to name an idea once and prove a hard step once.
4. Generics with concepts for the same body at several types; parameters or metaprograms for bodies that differ in constants or structure.
5. Assertions as stepping stones that split a hard goal.
6. Escape hatches last: `assume`, wrapping arithmetic that is not meant to wrap, `--allow-unproved`, `unsafe`.

The order is the order of proof cost: a type is checked where a value is made and then never again, a contract once in the callee and again at every call, a lemma once, an assertion as one more goal, and an escape hatch not at all. The page states each opinion with its measured cost, and keeps a catalogue of where the repository's own code still goes against one.

These are opinions. Nothing in this ADR makes a program that was accepted before an error.

### Lints

A lint is a warning with a name, a message that says what is better and why, and, where the change is mechanical, a fix. They live in `src/syntax/Lint`, on the syntax tree before metaprograms expand it, so `piac` and `pia-lsp` share them without LLVM and they point at the code the user wrote, not at generated code. `piac --check`, `--verify` and every `--emit` mode print them to stderr; `pia-lsp` publishes them as warnings from `pia-lint` and offers the fixes as quick fixes.

| Lint | Warns about |
| --- | --- |
| `range_requires` | a `requires` that bounds one parameter, or every element of a slice parameter, by constants |
| `range_ensures` | an `ensures` that bounds the result by constants |
| `redundant_bound` | a bound its type already states |
| `generic_candidate` | the same body as another function at other types |
| `metaprogram_candidate` | a body that differs from another only in its constants |
| `duplicate_function` | the same signature and body as another function |
| `derivable_eq` | a hand-written field-by-field equality on a record |
| `nonlinear_contract` | a product of two variables in a precondition's inequality, or a division by a variable in any contract |
| `deep_fuel` | `@fuel(n)` above 4 |
| `assume` | `assume` |
| `costly_goal` | after verification, a goal that cost 10% or more of the solver's resource limit |

The bound lints are deliberately narrow. They fire only in `@overflow(proof)` functions, since wrapping at a range would wrap at the range; not on `mutable`, `out` or `inout` parameters; not in spec functions, lemmas or metaprograms; and not for a one-sided bound on a type wider than 16 bits, which would have to be written `int{3..18446744073709551615}`. The message notes when the range type is stored in a narrower machine integer, which changes the C signature, and when the parameter is used in arithmetic with nothing wider expected, where the fix is not marked preferred. A fix moves the bound into the type and removes the clause, or only the conjuncts it moved, keeping the rest of the clause as written.

`nonlinear_contract` leaves products in postconditions alone, since there they are usually the specification itself, as in a saturating multiply.

`costly_goal` needs each goal's cost, so `piac` now always records it and prints it in the report only with `--solver-cost`. The threshold is `--costly-goal=<n>`, by default a tenth of `--solver-rlimit`, and `0` turns it off. Its advice depends on the goal: lemmas and `assert` steps for postconditions and invariants, range types at the callee for preconditions, and range types or a helper function for overflow and bounds.

A function opts out of a lint with `@allow(<name>)` on its return annotation; IRGen accepts and ignores it. `--no-lint=<name>` turns one off for a run, and `--no-lint` turns all of them off.

### Statistics by origin

`--verify-stats` adds `type`, `type_smt`, `type_cost`, `contract`, `contract_smt` and `contract_cost`. Type goals are raised by operations on typed values: overflow and narrowing into a range type, bounds, divisors, shifts, match exhaustiveness and out parameters. Contract goals are written: preconditions at calls, postconditions, loop invariants, measures, assertions and concept laws. Moving facts into types shows up as fewer contract goals sent to the solver, and the build-time benchmark can follow it.

### Decomposed reasoning

The page also states how to keep each query small, since every goal is its own query (ADR 0032): functions are proof boundaries, so a loop body with its own contract is proved once; preconditions should stay linear, since every goal assumes them; `assert` splits a hard goal; `--verify-only` and `--proof-cache` keep iteration fast; and `costly_goal` names the goals worth splitting.

## Consequences

- Constant preconditions in the docs became range types or relational contracts where that read better. Tests keep them, because they test contracts. Running the lints over `docs/` found the remaining cases listed on the page: the stream demo's parallel `fill`/`dem` slices and its `bound < 4294967295`, and the VecDeque case study's one-sided `0 < old_cap`.
- Every `piac` run that compiles or verifies may print warnings. A test that checks stderr for the absence of warnings passes `--no-lint`, as `tests/codegen/lower.pia` does.
- The lints are syntactic, so they can be wrong about meaning: they do not see type aliases, and they cannot tell whether a duplicated body uses operations a concept could name. They are warnings for that reason.

## Follow-ups

These would make the types-first opinion cheaper to follow, and are tracked as issues:

- **Arithmetic on ranges at an exact range.** ([#151](https://github.com/deanberris/pia-lang/issues/151)) An operation on range-typed operands with nothing wider expected could produce the exact interval of its result (`x - 1 : int{0..63}` for `x : int{1..64}`), which intervals already compute, and a literal could take its own value's range. Then a range type would never make code that was proved fail.
- **Intervals for preconditions.** ([#152](https://github.com/deanberris/pia-lang/issues/152)) A callee's precondition that only bounds a parameter by constants could be discharged by the argument's range, as narrowing already is, without a solver query.
- **Ranges with an open side,** ([#153](https://github.com/deanberris/pia-lang/issues/153)) such as `u32{1..}` or `usize{3..}`, so one-sided bounds on wide types can be types too.
- **More type-level facts:** record `where` invariants and refinement types, which would let the lints move relational facts, such as `lo <= hi` on a record, into types as well.
