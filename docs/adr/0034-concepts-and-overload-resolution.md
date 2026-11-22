# 34. Concepts as checked signatures, and concept-based overload resolution

Date: 2026-11-22

Status: Proposed

## Context

[ADR 0009](0009-generics-concepts-adapters.md) decided that constraints on type parameters are concepts: checked metaprograms that can state laws, which every instance proves, with adapters for types that do not meet them. Generic types and generic functions landed in [PR #137](https://github.com/deanberris/pia-lang/pull/137), but without constraints. A generic body can use any operation, and an instance only fails when it is generated. The standard library needs concepts before it can be written generically: `Eq`, `Ord` and `Hash` for containers, `Numeric` for reductions, and `Allocator` for `Pia.Mem` ([ADR 0026](0026-memory-manager.md)).

Dean asked for concept-based overload resolution as the step after concepts, because it is what lets a library offer one name with several implementations, and lets the most specific one win. He also asked that constraints, specifications and contracts disambiguate by what they say, not only by named subsumption. Examples: a `sort` for any `Ord t` and a faster one for `Radix t`, or a `copy` that becomes a `memcpy` when its buffers are proved disjoint.

The existing sketches disagree on syntax. design.md writes a concept as a metaprogram over `has_fn` and `law` predicates, and stdlib.md writes `Allocator` as a `sig ... end`. Pia also has no overloading of any kind yet: a name means exactly one top-level function.

## Decision

### Concepts

A concept is a metaprogram that takes types and returns a signature, the same `sig ... end` that interfaces use. Each requirement is a function with a type and, optionally, a contract. A law is a `lemma`, as in the spec functions of [PR #133](https://github.com/deanberris/pia-lang/pull/133), and `include` brings in another concept's requirements:

```ocaml
let meta Eq (t : type) : concept = sig
  let eq : (a : t) -> (b : t) -> bool
  let lemma reflexive (a : t) ensures eq a a
  let lemma symmetric (a : t) (b : t) ensures eq a b ==> eq b a
end

let meta Ord (t : type) : concept = sig
  include Eq t
  let lt : (a : t) -> (b : t) -> bool
  let lemma irreflexive (a : t) ensures lt a a = false
  let lemma transitive (a : t) (b : t) (c : t)
    ensures lt a b && lt b c ==> lt a c
end
```

Because a concept is a metaprogram, its body can compute the signature, for example adding a requirement only when `size_of t` is small, or stopping with its own diagnostic (`fail "f16 has no total order"`). The first implementation accepts a literal `sig` with the parameters spliced in. The `has_fn` and `law` sketch in design.md is replaced by this form, which is one syntax shared with interfaces ([ADR 0024](0024-published-proof-certificates.md)) and lets a requirement carry a contract.

A constraint goes on the type parameter, as design.md already shows: `(t : type where Ord t)`, with `&&` for several (`where Eq t && Hash t`).

### Meeting a concept

A type meets a concept when every requirement, with the type arguments substituted, is met:

- **A function requirement** is met by a function in scope with that name and exactly that signature: the same parameter types, modifiers and result type. Scope is the type's own module plus imported modules, the ADL rule of [ADR 0022](0022-metaprogram-hygiene.md). If the requirement has a contract, the candidate must honour it, and that is proved: the requirement's `requires` implies the candidate's, and the candidate's `ensures` implies the requirement's. A candidate with no contract of its own meets only requirements with no `requires`, and only `ensures` it can be proved to satisfy from its body.
- **A law** is proved once per instance, as a lemma whose body is checked against the instance's functions. There is no `@assume` escape (ADR 0009).
- **An included concept** must be met as well, and its requirements are part of this one.

The check runs when a generic is instantiated (the use check). A failure names the concept, the requirement and the type, as in "u8 does not meet Ord: no function 'lt : u8 -> u8 -> bool'", or gives the law's counterexample.

### Adapters

An adapter supplies a concept's requirements for a type that does not meet it, or meets it in the wrong way, such as `f32`, whose `=` fails `reflexive` on NaN:

```ocaml
let adapter bitwise_eq : Eq f32 = struct
  let eq (a : f32) (b : f32) : bool = bits a = bits b
end
```

An adapter's functions and laws are proved like any other instance. It can live in any module. A type that meets a concept directly uses its own functions, and an adapter is used only when it is named (`dedup<t = f32, Eq = bitwise_eq> xs`) or when it is the only way the type meets the concept. Two adapters for the same concept and type in scope, with neither named, are an ambiguity error that names both.

### Definition check

A generic body may use only what its constraints promise. A call whose arguments have a constrained type parameter's type resolves against the requirements of that parameter's concepts (including the included ones), and against other generic functions whose constraints those concepts imply. Anything else is an error at the definition: in `let max (t : type where Eq t) (a : t) (b : t) : t = if lt a b then b else a`, the error is that `lt` is not promised by `Eq t`, with a hint to constrain `t` by `Ord t`.

The binding is made at the definition. The instance `max<u8>` calls the function that met `Ord u8` at the use check, whatever else is in scope when it is generated, so an instance can never pick up a different `lt` than the one the concept checked.

Each instance is still proved on its own, so goals stay about concrete types. Proving a generic body once against the concepts' contracts would save build time ([ADR 0032](0032-parallel-sliced-cached-proving.md)). It is sound once requirement contracts are proved at the use check, and it is left as a measured follow-up.

### Overloading

Several top-level functions may share a name. They form an overload set, and they may differ in their parameter types, in their constraints, or only in their contracts. This is not shadowing in the sense of ADR 0022: no name hides another, every overload is visible, and a call chooses among them. Two overloads with the same parameter types whose preconditions are equivalent (each proved to imply the other), or two generics with the same parameter patterns and equivalent constraints, are an error at the second definition, because no call could ever choose between them.

Types, concept constraints and contracts all take part in choosing. A call resolves in three steps.

1. **Viable candidates.** For each overload with the right number of arguments, deduce its type arguments as today (explicit arguments, then the arguments' types, then the expected type). A candidate is viable if deduction succeeds, every argument converts to its parameter type, every constraint is met by the deduced types, and its precondition is proved at the call, from everything the verifier knows there: the caller's own `requires`, the path conditions of the branches the call is under, loop invariants, and the `ensures` of earlier calls.
2. **Ranking.** Candidate A is better than B if it is at least as good for every argument and better for one, or else equal on arguments and more specific. The tests apply in order, and the first that tells A and B apart decides:
   - per argument, an exact type match is better than a conversion (such as a literal's or a widening);
   - a non-generic function is more specific than a generic one;
   - between generics, A is more specific if A's parameter types are an instance of B's but not the reverse: `f (xs : [u8])` over `f (t : type) (xs : [t])`, and `f (p : pair t t)` over `f (p : pair a b)`;
   - A is more specific if its constraints entail B's and not the reverse (see below): `sort (t : type where Radix t)` over `sort (t : type where Ord t)`;
   - A is more specific if its precondition implies B's and not the reverse. With `copy (dst : out [u8]) (src : [u8]) requires disjoint dst src` and a `copy` with no precondition, a call where the buffers are proved disjoint gets the first (a `memcpy`), and any other call gets the second (a `memmove`).
3. **Choice.** The unique best viable candidate wins. No viable candidate is an error that lists each overload and why it failed: wrong arity, deduction, conversion, an unmet requirement, or an unproved precondition with its counterexample. Two or more best candidates are an ambiguity error that lists them, and suggests explicit type arguments or a fact that would separate them.

**Entailment between constraints** is decided from what concepts say, not only from their names. A's constraints entail B's when every concept in B's is entailed by one in A's. Concept C entails concept D:

- at once, if `include` reaches D from C. This is the cheap, common case;
- otherwise, if every requirement of D has a match in C with the same name and signature and a contract at least as strong (D's `requires` implies C's, and C's `ensures` implies D's), and every law of D follows from C's laws and contracts. Both are proved by the solver, over the concepts' type parameter left abstract, once for each pair of concepts. The result is part of the module's proof certificate and is cached like any goal.

So two concepts that say the same thing under different names entail each other, and an overload set that differs only by such concepts is rejected at its definition as never able to choose. Laws take part through entailment: `Ord` with a `transitive` law entails a `Preorder` whose only law is `transitive`.

**Precondition order** between overloads, A's `requires` implying B's, is proved once per pair when the overload set is defined, with the parameters universally quantified, so calls do not repeat it.

**Choosing by contract is static.** It happens at compile time, from proofs, and never adds a run-time test. A program that wants to test at run time writes the `if` itself, and each branch then calls the overload its path condition proves. A candidate's `ensures` never makes it viable: what a call means cannot depend on what the caller goes on to prove with its result.

**Where it runs.** IRGen ranks by types and by constraints, which need no proof of the call site. Only when candidates are still tied, and their preconditions differ, does IRGen leave the call open: a `func.call` of the least specific candidate that names them all, most specific first, in a `pia.overload_candidates` attribute. The verifier chooses at that point of the function, where it has the path facts, and retargets the call before verification and code generation. (This was first sketched as a `pia.overload_call` op; an attribute on the call keeps the IR valid, and the least specific candidate correct, before the choice is made.) These choices are part of compiling, not of optional verification: `piac --emit=obj` without `--verify` still decides them, `--verify-only` still decides every choice in the selected functions, and an `--allow-unproved` flag never makes a candidate viable. Each choice costs one query per tied candidate, run in parallel on ADR 0032's pool and cached by its proof cache, and calls whose types already decide cost nothing.

**In a generic body**, a choice by contract can use only facts that hold in every instance: the body's own contracts and path conditions, and the requirement contracts of its constraints. Every instance therefore makes the same choice, the one the definition check made.

Explicit arguments narrow the candidates before ranking, so `sort<t = u32, Ord = by_value>` can force the general overload for a type that also meets `Radix`.

### Symbols

An instance of a generic is named after its type arguments, `max<u8>`, as today. When a name is overloaded, every overload's symbol also carries its parameter types, `eq(u8, u8)` and `eq(pixel, pixel)`, and so does its C entry point, as `eq__u8_u8`. Overloads with the same parameter types, told apart by contracts, add their position in the set: `copy(out [u8], [u8])#2`. A name that is not overloaded keeps its plain symbol and entry point, so existing C callers do not change. The published interface of ADR 0024 lists overloads separately, and adding an overload to a module changes its interface hash.

## Consequences

- Library code can be generic and checked at its definition, and a missing operation is reported where the generic is written, not deep inside an instance.
- Overloading lands with concepts, not after them, because structural matching needs it: `eq` for `u8` and `eq` for `pixel` are both requirements' candidates, so they must coexist under one name. `@derive(eq)` then generates an `eq` overload instead of `eq_<name>`, and the record `=` expands to `eq`.
- Ranking is a partial order, so some overload sets have no best candidate for some calls. Those are reported as ambiguity at the call, with the candidates listed, rather than resolved by declaration order.
- Every requirement contract and every law adds proof goals per instance. They are proved once per (concept, type) pair, not once per use, and they are cached by ADR 0032's proof cache like any other goal.
- Name lookup in a generic body is fixed at the definition, so adding a function to a module can never change what an existing instance calls. It can only make a future call ambiguous, which is reported.
- Overload resolution can need the solver, so the solver is on the path of every build, not only of `--verify`. Types decide most calls with no query, and the queries that remain are small (one precondition at one call), parallel and cached.
- Implementation order: (1) overloading of concrete functions by parameter type, with symbols and C entry points; (2) `sig` concepts, `where` constraints, the use check, `include`, requirement contracts and laws; (3) the definition check; (4) adapters; (5) ranking by constraints, with entailment by `include` and then by proof; (6) choosing by precondition in the verifier, with `pia.overload_candidates`. Each is a PR with its own tests.
