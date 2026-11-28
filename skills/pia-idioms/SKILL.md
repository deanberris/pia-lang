---
name: pia-idioms
description: Act on Pia's lint warnings (range_requires, generic_candidate, nonlinear_contract, costly_goal and the rest) and shape code so its proofs stay cheap - which rewrite each lint wants, when to keep the original with @allow, and how to split costly goals. Use when piac or pia-lsp prints a `warning: ... [name]`, when reviewing Pia for idiom, or when a proof is slow.
---

# Pia idioms and lints

Idiomatic Pia states each fact as early as it can be said: in a type, then a contract, then a spec function or lemma, then a generic or metaprogram, then an `assert`, and an escape hatch last ([ADR 0037](../../docs/adr/0037-idiomatic-pia-and-lints.md)). The earlier rungs are also the cheaper proofs, so following the lints makes a file prove faster. `pia-language` has the ladder with examples; [docs/idioms.md](../../docs/idioms.md) has the measurements behind it.

Lints are opinions, never errors. They print to stderr as `file:line:col: warning: ... [name]`, often with a `fix:` line that `pia-lsp` offers as a quick fix. They run on the program as written, before metaprograms expand it, in `piac --check`, `--verify` and every `--emit` mode.

## What each lint wants

| Lint | You wrote | Rewrite to | Keep it when |
| --- | --- | --- | --- |
| `range_requires` | `requires x <= 100`, or `forall k. xs.[k] < 16` | `(x : int{0..100})`, `(xs : [int{0..15}])` | the bound mirrors a C signature that must not change size |
| `range_ensures` | `ensures result < 16` | a return type `int{0..15}` | the result's C type is fixed |
| `redundant_bound` | `requires x >= 0` on a `u8` | delete it | never |
| `generic_candidate` | the same body at `u8` and `u16` | one function `(t : type where C t)` | the copies are meant to diverge |
| `metaprogram_candidate` | bodies that differ only in constants | range-typed parameters, or a `let meta` that generates them | the constants are a public table |
| `duplicate_function` | an exact copy | a call | never |
| `derivable_eq` | a field-by-field equality | `@derive(eq)` on the type | the equality is deliberately partial |
| `nonlinear_contract` | `requires w * h <= n`, or `/ n` in a contract | range-typed factors, a helper with `@overflow(saturate)` and a linear contract, or a lemma | rarely: every goal in the function pays for it |
| `deep_fuel` | `@fuel(n)` above 4 | a lemma proved by induction with `decreases` | n is 5 or 6 and the spec is tiny |
| `assume` | `assume p` | `requires p` if callers can promise it, `assert p` or a lemma if it follows | a `@trusted` file stating a platform fact |
| `costly_goal` | a goal costing 10% or more of the solver limit | split it (below) | never; raise `--costly-goal` only to silence a known one in CI |
| `needless_rec` | `let rec` on a type that is not recursive | `let` | never |
| `repeated_contract` | a definition repeats its interface's contract exactly (parameter names aside) | delete the definition's `requires`/`ensures`/`costs`/`reads`; it takes the interface's (ADR 0077) | never; a stronger contract is not flagged |

To keep a form deliberately, put `@allow(name)` on the function's return annotation, with a comment saying why:

<!-- example: narrow.pia -->
```ocaml
let narrow (x : u32) : u8 @allow(range_requires)
  requires x < 256   \ kept as a contract: it mirrors the C API
= x
```

`piac --no-lint=name` turns one off for a run and `--no-lint` turns them all off, which is for tests that check output, not for silencing advice.

A `warning: ... [deprecated]` is not a lint: it names a migration rule, and the old form it flags stops compiling in the next release. Apply its quick fix, or run `piac migrate` on the file ([docs/migrations.md](../../docs/migrations.md)); no flag turns it off.

## The lint in practice

<!-- example: percent.pia -->
```ocaml
let scale (p : u8) : u16
  requires p <= 100
= p * 3
```

```console
$ piac --check percent.pia
percent.pia:2:3: warning: this precondition only bounds 'p' by constants; say it in the type instead, (p : int{0..100}), so the fact travels with the value and intervals can use it [range_requires]
    requires p <= 100
    ^
  fix: Move the bound into the type: (p : int{0..100})
```

After the fix, `p * 3` is decided by intervals instead of Z3, a caller whose value already has a narrower range passes it with no goal at all, and the value keeps the fact after the call. Two things change with the type: it is stored in the smallest integer that holds it (a C signature can change), and arithmetic with nothing wider expected happens at the range, so write `let d : u16 = p - 1 in`, not `let d = p - 1 in`.

## Keeping proofs cheap

Each goal is its own solver query, carrying the function's preconditions and everything before it. To keep queries small:

- **Functions are proof boundaries.** Move a loop body with a hard goal into a function with its own contract; the loop then sees only the contract.
- **Keep preconditions linear and quantifier-free.** A `forall` or a product in a `requires` is assumed in every goal of the function. Use element ranges and range-typed factors instead.
- **Split with `assert`.** An `assert` before a hard postcondition is proved on its own and then assumed.
- **Prefer a variant to a tag, a slice to a pointer and length, and a slice of records to parallel arrays.** Each removes a contract every caller would prove.
- **Measure.** `piac --verify --verify-stats` splits goals into those the types raised and those the contracts stated, with their costs, `--solver-cost` prints each goal's Z3 resource count, and `--goal-times` how long each took. `pia-fast-proofs` has the rest: `--verify-only`, `--proof-cache`, `--jobs`.

## Escape hatches, last

`assume` only in a `@trusted` file, listed by `--trust-report`; `@overflow(wrap)` only for arithmetic that is really modular (hashes, checksums); `--allow-unproved` only for a goal the verifier cannot prove yet, named one at a time; `unsafe` only to call a C function that has no contract. Each is a trusted item that a reader of the trust report has to accept.
