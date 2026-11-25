# 69. Pure and impure functions: computed purity, `@pure` assertions, and `@impure` interface boundaries

Date: 2026-11-25

Status: Accepted (2026-11-25)

## Context

Issue [#375](https://github.com/deanberris/pia-lang/issues/375) showed that when an ordinary function returning a record — such as `Pia.Time.civil_from_days` — is named more than once in a contract, the verifier encoded each mention as an unrelated fresh value. The interface conformance check substitutes `result` with a call at every mention, so `ensures days_from_civil result.year result.month result.day = z` became three separate calls whose fields were never tied together.

Inside a single module, the verifier can walk a function's body and call graph to decide whether it is deterministic. **Across a module boundary, it cannot.** Today a `.piai` interface ([ADR 0039](0039-module-and-interface-syntax.md)) carries no purity information:

- `Pia.Sys.Posix.open`, `close`, `lseek` and `errno` take no `out` or `inout` parameters, yet wrap `extern` C syscalls with observable side effects (file descriptors, global `errno`, OS state).
- `Pia.Time.civil_from_days` is genuinely pure, yet an importer sees the same kind of signature as `Posix.open`.
- Existing `contractOnly` in `src/verify/Verifier.cpp` encodes every single-scalar imported function as one uninterpreted function, which is unsound for impure scalar FFI wrappers such as `Posix.close` or `Posix.errno` when called more than once.

At the same time, programmers have no way to *assert* that a function is pure and have the compiler reject an accidental side effect, nor to see from an interface whether an exported function has hidden effects.

## Decision

### 1. Three levels of purity, computed by the compiler

Every function in Pia has a purity level **computed by the compiler** from its signature, its body and its transitive call graph:

1. **Strongly pure (total, no effects).** Takes no `out`, `inout`, `mutable`, `atomic` or `dyn` parameters; performs no hidden effects (section 2); and is proved to terminate (every `while` loop and recursive cycle has a `decreases` measure, matching [ADR 0043](0043-generic-definitions-proved-once.md) and [ADR 0044](0044-function-values-and-lambdas.md)). Local mutation (`let mutable` locals, non-escaping local buffers from `with_arena`, and calling weakly-pure functions on local buffers) and returning fixed arrays `[T; N]` are allowed: repeated calls on equal arguments always return equal values and change no observable state outside the call.
2. **Weakly pure (parameter mutation only, total).** Takes one or more `out`, `inout` or `mutable` parameters, performs no hidden effects, and is proved to terminate. Examples include `Algo.Sort.sort` and `Vec.push`. Its effects are completely visible in its parameter modifiers, so it needs no `@impure` attribute and may be called on local buffers inside a strongly-pure function. It cannot be called directly in contracts.
3. **Impure (`@impure`).** Performs or transitively calls any hidden, concurrent, or potentially non-terminating effect:
   - any foreign `= extern "..."` declaration (always impure; see section 3),
   - any `unsafe` call or `unsafe view`,
   - any pointer-address operation (`AddressOp` / `AtAddressOp`),
   - any atomic operation or `atomic` parameter ([ADR 0052](0052-atomics.md)),
   - any `while` loop or recursion without a proved `decreases` measure,
   - any call to an impure function (including imported `@impure` functions).

Calls to `let spec` functions and `let lemma` proofs never make a function impure.

### 2. `@pure` and `@impure` attributes

```ocaml
(* Private functions infer purity automatically; no attribute is needed. *)
let civil_from_days (z : int{-365962028..364523337}) : ymd = ...

(* Optional @pure asserts strong purity + totality; violation is an error. *)
let civil_from_days (z : int{-365962028..364523337}) : ymd @pure = ...

(* Exported impure functions must declare @impure in their interface. *)
interface Posix = sig
  let open : (path : [u8]) -> (flags : i32) -> i32 @impure @variadic(2)
    requires len path >= 1 && path.[len path - 1] = 0
    ensures result >= -1
  let close : (fd : i32) -> i32 @impure
    ensures result >= -1 && result <= 0
end
```

- **Private functions:** purity and impurity are computed automatically, so private helpers and atomic primitives (such as `tests/verify/atomics.pia`) need no annotation.
- **`@pure`:** an explicit, compiler-checked assertion of **strong purity and totality**. Placing `@pure` on a function that takes `out`/`inout`/`mutable` or `atomic` parameters, performs a hidden effect, calls an impure function, or lacks proved termination is a compile-time error.
- **`@impure`:** explicitly declares hidden, concurrent or non-terminating effects.
- **Lint ([ADR 0037](0037-idiomatic-pia-and-lints.md)):** a lint (`impure_interface`) recommends adding `@impure` on definitions and interface rows whose computed purity is impure when they are part of a module's interface, so the annotation stays visible at the definition as well as the interface.

### 3. Foreign (`= extern "..."`) functions are always `@impure`

Every `= extern "..."` declaration is unconditionally `@impure`. Marking a foreign declaration `@pure` is a compile-time error, even inside a `@trusted` module: pure functions are proved in Pia (or modelled as a library theory, [ADR 0036](0036-library-theories.md)), never trusted through C FFI. Purity therefore adds zero unverified trust surface to `--trust-report`.

### 4. Interfaces, `.piai` export and conformance

Matches [ADR 0004](0004-strongest-guarantee-by-default.md) ("the strongest guarantee is always the default; every weakening is visible in the source and, where it affects callers, in the interface"):

- **Unmarked interface rows default to non-impure** (strongly pure when there are no `out`/`inout`/`mutable` parameters; weakly pure when there are). An implementation whose computed purity is impure **fails interface conformance** unless the interface row carries `@impure`.
- **Subtyping:** a strongly-pure (or weakly-pure) implementation satisfies an `@impure` interface row (stronger meets weaker, matching weaker `requires` and stronger `ensures`). An impure implementation cannot satisfy an unmarked or `@pure` interface row.
- **Always exported in `.piai`:** the compiler always writes the computed purity property into `.piai` interface artifacts and includes it in the interface hash ([ADR 0024](0024-published-proof-certificates.md)). Importers always know statically whether an imported function is strongly pure, weakly pure or `@impure`.

### 5. Contracts and verifier encoding

- **No impure calls in contracts:** calling an `@impure` function (or a weakly-pure mutating function) inside `requires`, `ensures`, `invariant`, `assert`, `let spec` or `let lemma` is a compile-time error — generalising [ADR 0044](0044-function-values-and-lambdas.md) section 6's ban on effectful lambdas in contracts.
- **Interface conformance for `@impure` functions:** an `@impure` function may still carry `requires` and `ensures` about its own `result` and parameters (such as `Posix.open`'s `ensures result >= -1`). Its conformance check uses `queueContractCall` (calling the function once as the body and checking `ensures` on `result`) rather than substituting calls into `ensures`.
- **Verifier uninterpreted-function encoding ([#375](https://github.com/deanberris/pia-lang/issues/375)):** strongly-pure functions — both module-local and imported — are encoded lazily as one uninterpreted SMT function per scalarized result field whenever called more than once or demanded in a contract or quantifier, so repeated calls (such as `civil_from_days z` in `Calendar.civil_from_days.contract`) agree. `@impure` imported functions (such as `Posix.close`, `Posix.lseek` and `Posix.errno`) are **never** encoded as uninterpreted functions, closing the `contractOnly` soundness gap.

### 6. Higher-order functions and purity polymorphism

Higher-order functions such as `map`, `fold` and `find` are generic over their callback's `Function` instance ([ADR 0044](0044-function-values-and-lambdas.md)) and monomorphised per callback:

- **Purity polymorphism:** an arrow parameter `(f : a -> b)` accepts either a pure or an `@impure` callback unless annotated `@pure` (or called in the higher-order function's contracts, which requires `f` to be strongly pure). Each monomorphised instance computes its purity from its body and the concrete callback `f`: `map xs f` is pure when `f` is pure and `@impure` when `f` is `@impure`.
- **Generic proofs ([ADR 0043](0043-generic-definitions-proved-once.md)):** a generic proved once whose contracts apply `f` requires `f` to be strongly pure and total; one whose contracts do not apply `f` holds for impure callbacks too.

### 7. Code generation

Once purity is checked by the compiler, LLVM lowering can attach `memory(none)` / `willreturn` attributes to strongly-pure functions where sound. Codegen remains unchanged in the initial steps.

## Dean's answers (2026-11-25)

1. **Default polarity:** pure by default (when no `out`/`inout`/`mutable` or `atomic` parameters), with `@impure` for hidden effects and optional `@pure` as an explicit checked assertion.
2. **Purity boundary:** externally pure and total — local mutation (`let mutable`, local buffers / `with_arena`) and fixed-array `[T; N]` returns are allowed, and purity requires proved termination (`decreases` on `while` and recursion).
3. **Foreign (`extern`) functions:** always `@impure`; no `@pure` on C FFI, even in `@trusted` modules. Pure code is written in Pia or modelled as a theory.
4. **Parameter mutation vs hidden effects:** D-style weak vs strong purity. Functions whose only effect is mutating `out`/`inout`/`mutable` parameters (like `sort`) need no `@impure` and may be called on local buffers inside pure functions; `@impure` marks hidden effects, and `@pure` asserts neither mutable parameters nor `@impure`.
5. **Computed purity, `.piai` export and lint:** purity/impurity is computed automatically by the compiler (including for atomics) and always exported in `.piai` interfaces; unmarked interface rows default to pure (hard conformance error if the implementation is impure), and a lint recommends writing `@impure` on exported impure functions.
6. **Higher-order functions:** include purity polymorphism (e.g. `map` inherits the purity of its callback).
7. **Rollout:** fold this ADR into the same PR as the `#375` verifier fix, then build the compiler checks in follow-up steps.

## Build order

1. **Verifier encoding for repeated pure calls ([#375](https://github.com/deanberris/pia-lang/issues/375), this PR):** lazy uninterpreted-function encoding per scalarized result field for module-local pure functions, with `tests/verify/pure_contract_calls.pia`.
2. **Computed purity, `@pure`/`@impure` attributes, and contract checks:** compute strong/weak/impure purity (including termination) in IRGen/Verifier, accept `@pure` and `@impure` in `genAttributes`, reject `@pure` on `extern` and impure calls in contracts/specs/lemmas, and route `@impure` interface conformance checks through `queueContractCall`.
3. **Interfaces, `.piai`, `Pia.Sys.Posix`, and `contractOnly` fix:** export computed purity in `.piai` and include it in the interface hash; enforce unmarked interface rows as non-impure; annotate `lib/Pia/Sys/Posix.pia` (and `tools/bindings/gen.py`) with `@impure`; restrict imported uninterpreted-function encoding in `Verifier.cpp` to strongly-pure imports.
4. **Lint and skills:** add the `impure_interface` lint in `src/syntax/Lint.cpp` (with `tests/lint/`), and document `@pure` and `@impure` in `docs/design.md`, `docs/idioms.md`, and `skills/pia-language/SKILL.md`.
5. **Purity polymorphism:** propagate callback purity through monomorphised higher-order functions and ADR 0043/0044 checks, with tests in `tests/verify/`.
6. **Codegen (optional follow-up):** emit LLVM `memory(none)` / `willreturn` attributes for proved strongly-pure functions.

## Consequences

- Purity becomes a compiler-computed, interface-visible property rather than a verifier-internal heuristic.
- Imported strongly-pure functions returning records (such as `Pia.Time.civil_from_days`) work in contracts across module boundaries, while impure FFI wrappers (`Pia.Sys.Posix`) cannot be falsely equated by the solver.
- Private functions and weakly-pure mutating algorithms (`Algo.Sort`, `Vec`, codecs) require no new annotations; only exported functions with hidden, concurrent, or non-terminating effects carry `@impure` in their interfaces.
- No unverified trust surface is added: `= extern "..."` is always `@impure`.

## Prior art

| Source | What Pia takes |
| --- | --- |
| D `pure` | Weak vs strong purity: local mutation and calling mutating helpers on local state inside strongly-pure functions |
| F* `Tot` / `Pure` vs `ML` / `Dv` | Pure and total by default, with explicit effectful boundaries |
| Dafny `function` vs `method` | Only pure total functions appear in contracts and act as SMT functions |
| Koka / Flix effect systems | Purity polymorphism for higher-order functions |
