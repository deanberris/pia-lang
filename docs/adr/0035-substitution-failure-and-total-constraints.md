# 35. Substitution failure removes a candidate, and constraints are proved to terminate

Date: 2026-11-22

Status: Accepted (Dean, 2026-11-22), on the condition recorded under "Matching on types"

## Context

[ADR 0034](0034-concepts-and-overload-resolution.md) chooses among overloads by types, constraint entailment and proved preconditions. Each candidate's type arguments are deduced and then substituted into its signature. Some signatures cannot be formed for some types. A result type may be computed by a type-level metaprogram that is defined only for some types, a `where` predicate may be false, or a concept's metaprogram may stop with its own diagnostic. Dean asked for Pia's version of C++'s "substitution failure is not an error" (SFINAE): such a candidate drops out instead of failing the build, on the condition that the constraints can be proved to terminate.

C++ shows what to avoid. Whether an error is a soft failure or a hard one depends on an "immediate context" that is hard to see. An error in a function body is always hard, so a candidate that passes its signature can still break the build inside its instance. And template recursion is cut off by an implementation's depth limit, so which overload is chosen can depend on the compiler. Pia's metaprograms ([ADR 0007](0007-metaprogramming-fixed-point-expansion.md), [docs/meta.md](../meta.md)) are cut off the same way, by a budget of a million interpreter steps.

## Decision

### What may fail softly

Substituting a candidate's deduced type arguments into its signature is the candidate's *substitution*. It covers:

- resolving each parameter type and the result type, including generic types and type-level metaprograms such as `widen t` below;
- evaluating its `where` constraints: concepts (ADR 0034), and compile-time predicates over types such as `size_of t <= 8`;
- proving the requirement contracts and laws that a concept constraint brings (ADR 0034, "Meeting a concept").

Any failure there, whether an unmet requirement, a `fail` from a metaprogram, a false predicate or a type that cannot be formed, removes the candidate from the call. It is not an error unless no candidate is left. The failure is kept as the candidate's reason, and the "no viable overload" error lists every candidate with its reason. `piac --explain-overloads=<file:line>` prints the reasons even when a candidate wins.

```ocaml
let meta widen (t : type) : type =
  if t = u8 then u16 else if t = u16 then u32 else if t = u32 then u64
  else fail (concat "no integer type is wider than " (name t))

let sum (t : type) (xs : [t]) : widen t = ...    (* never overflows *)
let sum (t : type where Numeric t) (xs : [t]) : t
  requires ...                                      (* the caller proves the bound *)
  = ...
```

`sum xs` with `xs : [u16]` gets the first overload, which returns a `u32`. With `xs : [u64]`, `widen u64` fails, so the first overload drops out and the second is the only candidate.

Nothing else fails softly. A body is never part of the substitution, and it does not have to be: the definition check of ADR 0034 proves that a generic body uses only what its constraints promise, so a body cannot fail for a type that met them. Errors in the body of a generic are reported once, at its definition, for every type. That closes the C++ gap where a candidate passes its signature and then breaks the build in its instance.

### Constraints are total

Which candidates survive must be a function of the types alone: the same in every build, on every machine, with any `--jobs`, and never decided by a step budget. So every metaprogram that runs during substitution must be proved to terminate. This covers concepts, type-level metaprograms used in a type, and `where` predicates. Such a metaprogram is *total* when:

- it calls only total metaprograms and the interpreter's builtins (`fields`, `name`, `map`, `fold`, `length`, `concat` and the rest are total: each walks a finite value once);
- it is not recursive, or each recursive call is on a strictly smaller argument, or it has a `decreases` measure.
  - **Structural recursion** is recognised without a proof: a call on a component of a type parameter (a field's type, a payload's type, an element type, a type argument of an instance) or on the tail of a list parameter. Types are finite trees, so this always ends.
  - **Anything else** needs `decreases m`, where `m` is an integer that is at least 0 and smaller at each recursive call. These goals are proved by the verifier exactly like the measures of spec functions ([PR #133](https://github.com/deanberris/pia-lang/pull/133)), with the metaprogram's integer and boolean code encoded the same way.
  - Mutual recursion needs one measure that every function of the cycle decreases, and until that is implemented it is rejected, as it is for spec functions.

Totality is checked once, where the metaprogram is defined. A metaprogram that is not total is still a metaprogram, and expansion can still run it under the step budget, but using it in a constraint or a type is an error at that use: "'widen' is used in a constraint, so it must terminate: the recursive call at 4:12 has no decreasing argument; add 'decreases ...'".

Constraint metaprograms are also pure: they inspect types and return a signature, a type, a boolean or a diagnostic, and they cannot add items to the program. So substitution cannot feed the expansion loop of ADR 0007, and `--meta-cycles` never affects which overload is chosen.

The step budget stays as a guard against interpreter bugs. Running out of it during substitution is an internal compiler error, never a substitution failure.

### Recursion through types

A constraint may require constraints on other types: `Eq (pair a b)` requires `Eq a` and `Eq b`. These obligations are also constraints, so they too must end. Each one must be on a strictly smaller type than the one that required it, which holds for components of the type by the same structural rule. A cycle that grows types, such as `C t` requiring `C (wrap t)`, is rejected at the concept's definition, because it has no decreasing measure.

### Matching on types

Accepted on a condition (Dean, 2026-11-22): metaprograms need a way to pattern-match on a type instead of cascading `if t = u8 then ... else if ...`. `match` already takes values, and types are values, so it takes a type too, with type patterns:

```ocaml
let meta widen (t : type) : type =
  match t with
  | u8 -> u16
  | u16 -> u32
  | u32 -> u64
  | [e] -> [widen e]                 (* a slice, binding its element type *)
  | option e -> option (widen e)     (* an instance, binding its arguments *)
  | _ -> fail (concat "no integer type is wider than " (name t))
```

- A type name (`u8`, `pixel`) matches exactly that type. `[e]` and `[e; n]` match a slice or an array and bind its element type (and length). A generic's name applied to patterns, as in `option e` or `result t e`, matches its instances and binds or matches their type arguments.
- A lower-case name that is not a type binds the whole type, and `_` matches anything. Kind patterns match by shape: `record fs` and `variant cs` bind the list of field or payload types, `int` matches every integer type. A name that is both a type and a binder is an error, as shadowing always is (ADR 0022).
- Types are an open set, so a type `match` must end with a catch-all. An arm after one that already covers it is an error, as for value `match`.
- The names a type pattern binds are components of the matched type, so a recursive call on them is structural recursion under "Constraints are total", with no `decreases` needed.
- It is core `match`, not a library metaprogram. Dean weighed a `switch` metaprogram and chose core `match` (2026-11-22); a library form would also have needed declared expression forms and type constructors as metaprogram values. It is ordinary metaprogram code, so it needs no new keyword, and the interpreter evaluates it arm by arm. A predicate can use it as well: `let meta small (t : type) : bool = match t with | u8 -> true | [e; n] -> n <= 16 && small e | _ -> false`.

**Arms carry contracts.** This is why the match is core and not a library form (Dean, 2026-11-22): a pattern can have a precondition and a postcondition, written between the pattern and `->`, with `result` naming the arm's value:

```ocaml
let meta widen (t : type) : type
  ensures size_of result > size_of t
=
  match t with
  | u8  ensures size_of result = 2 -> u16
  | u16 ensures size_of result = 4 -> u32
  | u32 ensures size_of result = 8 -> u64
  | [e; n] requires n <= 4096 -> [widen e; n]
  | _ -> fail (concat "no integer type is wider than " (name t))
```

- `requires c` on an arm is not a guard: it does not decide which arm runs. It is an obligation on every value that reaches the arm, proved where the `match` is. For a type match it is checked when the arm is taken, and a false one is the candidate's reason under soft failure, so a constraint can say why a type does not fit.
- `ensures d` on an arm is proved for that arm's value, and after the `match` it is known under the arm's pattern: `t = u8 ==> size_of result = 2`. For a type-level metaprogram this is what the definition check of ADR 0034 is missing: it relates `widen t` to `t`, so a generic body that uses `widen t` can be checked once, from the arm postconditions and the metaprogram's own `ensures`, instead of in every instance.
- The same syntax applies to a value `match` in ordinary code, where both are verifier goals: `| Some x requires x < len xs -> xs.[x]` proves the bound at the `match` for every value that can be `Some x`, and `| Err e ensures result = 0 -> 0` adds a fact to the `Err` path. A handler's arms are a value `match`, so they take contracts too, proved once per `?` that reaches them (ADR 0028).

It is scheduled alongside `?` and the error handlers (#84).

### Results are cached

A candidate's substitution result, viable with its instance's signature or failed with its reason, depends only on the candidate and the type arguments. It is computed once per pair in a build, and its proof goals (requirement contracts and laws) go through the proof cache of [ADR 0032](0032-parallel-sliced-cached-proving.md) like any other goal.

## Consequences

- A library can offer an overload that only exists for some types, and fall back to another, without users writing explicit dispatch, and the choice is the same everywhere.
- Error messages for "no viable overload" can always say why each candidate failed, since every failure is a recorded reason rather than an aborted instantiation.
- Some useful metaprograms need a `decreases` measure before they can be used as constraints. Structural recursion over types and lists, the common case, needs nothing.
- Because bodies never fail softly, a generic's body errors are always reported at its definition, never at a use. That depends on the definition check of ADR 0034 landing first.
- Implementation order, after ADR 0034's steps: (1) type-level metaprograms in signatures, and `where` predicates; (2) the totality check (purity, builtins, structural recursion, then `decreases` with verifier goals); (3) soft failure in overload resolution, with recorded reasons and `--explain-overloads`. Step (3) needs (2), so that soft failure is never decided by a step budget.

## Implementation notes

- Step 1 (type-level metaprograms in types, and `where` predicates): a `where` predicate is any conjunct that is a comparison, a connective other than `&&`, or a call of a type-level metaprogram returning `bool`; a false one removes the candidate with its reason. Until steps 2 and 3, a metaprogram's failure in a type or a predicate is a hard error. In the definition check, a type-level metaprogram applied to a type parameter gives a stand-in type, and a signature that has one is checked in each instance rather than once, since nothing yet relates `widen t` to `t`; concept requirements that mention type-level metaprograms would close that gap. A generic whose constraints state every predicate of another's is the more specific, and a generic body may only call a generic whose predicates its own constraints state.
- Step 2 (the totality check): structural recursion is recognised on `element p` and on the elements of `field_types p` and `type_args p` that `map` or `fold` hand to a lambda, transitively. Since a type-level metaprogram's parameters are all types, an integer `decreases` measure has nothing to measure yet; it waits for metaprograms with value parameters in constraints. Local functions may not recurse, `listing` and `redefine` are impure, and a cycle between metaprograms is rejected.
- Matching on types (the acceptance condition), with arm contracts on type and value matches: not implemented yet; it comes alongside `?` and the error handlers (#84).
- Step 3 (soft failure): a metaprogram's `fail` while a candidate's signature is substituted, or while its predicates are evaluated, removes the candidate with the reason. Running out of steps there, and a use of a metaprogram that may not terminate, stay errors. Results are not cached per candidate and type arguments yet; concept checks already are. `--explain-overloads=<file:line>` prints the candidates, their reasons and the choice, as notes.
