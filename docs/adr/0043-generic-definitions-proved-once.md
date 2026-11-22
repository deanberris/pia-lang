# 43. Generic definitions are proved once, against their concepts

Date: 2026-11-22

Status: Proposed

## Context

[ADR 0034](0034-concepts-and-overload-resolution.md) gave Pia concepts, constrained generic functions and a *definition check*. It left one thing for later: "Each instance is still proved on its own, so goals stay about concrete types. Proving a generic body once against the concepts' contracts would save build time ([ADR 0032](0032-parallel-sliced-cached-proving.md)). It is sound once requirement contracts are proved at the use check, and it is left as a measured follow-up." The standard library ([ADR 0040](0040-cpp23-standard-library-in-pia.md)) is the measurement. Issue #203 records it.

### What happens today

Generics are monomorphised before verification:

1. **Definition check** (`IRGen::checkDefinition`). Each generic body is generated once, with each type parameter standing for a *stand-in* type, a record named after the parameter with no fields. A call whose arguments have a stand-in type resolves only against the requirements its constraints promise. That is a name and use check, so the body can only call what its concepts promise. The generated function, and every instance it made, is then erased. Nothing about it reaches the verifier.
2. **Instances** (`IRGen::genericInstance`). Each use with new type arguments queues an instance, `lex_compare<u8>`, generated after the function that first used it. An instance is an ordinary function at concrete types, with the requirement calls bound to the functions that met the concept at the use check.
3. **Laws** are lemmas generated per type at the use check, such as `Ord<u8>.irreflexive`. Each is proved once per type that meets the concept. A requirement's contract, such as `less`'s `ensures result ==> less b a = false`, is also a lemma per type (`Ord<u8>.less.contract`).
4. **The verifier** sees only instances. Each is encoded at its own types: 68-bit (or wider) bit-vectors, SMT arrays from index to element for slices, and records replaced by their fields. The proof cache ([ADR 0032](0032-parallel-sliced-cached-proving.md)) keys on the SHA-256 of each query, which mentions the types' widths and ranges. So two instances never share a cache entry.

### What it costs

- **Re-proof at every instance.** Splitting `lib/Pia/Core/Order.pia`'s cost by the definition each goal belongs to:
  - The generic `lexicographical_compare` (a loop with an invariant over a recursive spec function) and its spec function `lex_from` were 96.6% of 73.1 million resource units: 60.3M and 10.4M, about 8.8M at each of 8 integer types.
  - Everything else was 2.4M: the concrete instances, the laws at 9 types, and the other generics.
  - The module now exports the lexicographic functions for `u8` only, so it costs 9.75M. Each further type would cost about 8.8M again, for a proof that says nothing new.
- **No proof without an instance.** This is accepted, with `0 proved, 0 failed`:

  ```ocaml
  let bad (t : type where Ord t) (a : t) (b : t) : bool
    ensures result = less b a
  = less a b
  ```

  With instances at `u8` and `u16` it is refuted twice. A library module whose generic nothing in it instantiates is never checked at all. So `Pia.Core.Option` makes a `u8` use only so that its generics are proved.
- **Laws are not facts in generic bodies.** A body cannot call `irreflexive a`: a law is a lemma per type, not something the body can name. `Pia.Core.Order` had to restate asymmetry as a contract on the `less` requirement (`ensures result ==> less b a = false`), which a body can use.
- **Generic functions cannot be exported.** An interface cannot list `(t : type where Ord t) -> ...` ([ADR 0039](0039-module-and-interface-syntax.md), step 3), partly because there is no proof of a generic to export. Each library module exports per-type instances, stamped out by a metaprogram, so every type an importer might need is proved and paid for in the library.

### Prior art

Dafny and Why3 verify a generic method once with each type parameter an uninterpreted sort, plus whatever the type's traits or clones provide. Verus does the same for Rust generics, with trait bounds as uninterpreted functions and `spec` trait methods. F\* checks a polymorphic function once. None of them re-verifies at instances, because parametricity makes the instance proofs redundant. Coq and Lean do the same by construction. C++ templates are the opposite, checked only at instantiation, and Pia's instance proofs inherited that model.

## Decision

A constrained generic function's body is proved once, at its definition, with each type parameter an uninterpreted sort and each concept function an uninterpreted function constrained by its requirement contract and the concept's laws. An instance is then proved by that proof, whenever its body is the generic body with the type parameters substituted. Bodies that use facts only a concrete type has fall back to the per-instance proof they get today.

### 1. The abstract encoding

The definition check already generates the body at stand-in types. The new step keeps that function, marks it `pia.generic_definition`, and verifies it:

- **Type parameters are sorts.** A stand-in type `t` is `(declare-sort t 0)` in the query, not a record, so ScalarizeRecords leaves it alone. Its values are constants of that sort. A parameter, a `let`, a value returned from a requirement call: none of them has a width, a range or a bit pattern.
- **Buffers of `t`.** `[t]` and `[t; n]` are SMT arrays from the index bit-vector to `t`, with their lengths as today. Indexing, slicing, views, `old` and the frame facts of `inout` buffers ([verifier.md](../verifier.md)) are unchanged, since they never looked at the element.
- **Generic types.** `option t` and `result t e` are SMT datatypes over the sorts, as variants are today over concrete payloads.
- **Concept functions are uninterpreted functions.** Each requirement `less : (a : t) -> (b : t) -> bool` of a constraint `Ord t` is `(declare-fun Ord.less (t t) Bool)`, shared by every call in the body. A call in code and a call in a contract are the same application, so the body's `less xs.[i] ys.[i]` and the contract's agree. That is what a code call gives a pure function today, after the change in #202.
- **Requirement contracts are hypotheses.** At each call, the requirement's `requires` is a goal and its `ensures` is assumed, as for any call. This is sound because the use check proves each requirement contract of each type that meets the concept (`Ord<u8>.less.contract`).
- **Laws are hypotheses.** Each law of each constraint, `irreflexive`, `less_transitive` and so on, is a universally quantified axiom over the sort in every query of the body. They are guarded the way theory axioms are ([ADR 0036](0036-library-theories.md)): relevance by the functions a goal mentions, the fallback to every axiom of the theory before a goal fails, and tracking for the unsat core. This is also where laws become usable in generic bodies: a body or a spec function can rely on transitivity without restating it as a contract. Laws may also be callable as lemmas (`irreflexive a`), which instantiates one without the quantifier.
- **Generic callees.** A call from one generic to another, `lex_compare<t>` from `lex_compare_three_way<t>`, uses the callee's contract at the sorts, as a call between concrete functions does.

The goals are the generic's own: overflow of `usize` arithmetic on indices, bounds, invariants, measures, postconditions. A goal about a value of type `t` can only come from what the body does with it, so it is about sorts and the concept functions alone.

### 2. What falls back to per-instance proof

The abstract encoding applies only to a body whose meaning does not depend on the type arguments beyond their concepts. The definition check already knows when it does not, because the same facts make it generate the body at stand-ins differently or not at all. A generic is *parametric* unless its body or signature:

- does arithmetic, comparison or `=` on a value of a type parameter without a concept promising it (today an error at the definition check, so these never reach the verifier);
- applies a type-level metaprogram to a type parameter in its signature, such as `: widen t` ([ADR 0035](0035-substitution-failure-and-total-constraints.md)). The definition check already sets `opaqueStandIn_` and checks these bodies per instance;
- matches on a type, uses `size_of`, `type_kind` or any metaprogram builtin that reads a type argument, or has a `where` predicate that is not a concept (ADR 0035);
- depends on layout (a published object layout, [ADR 0030](0030-published-object-layouts.md)), on an element's bit width (`bits`, `bswap` on `t`), or on a constant of type `t`;
- is chosen between precondition overloads inside its body by facts that differ per instance. ADR 0034 already restricts a choice in a generic body to facts that hold in every instance. So this is the existing rule, and the abstract proof makes the same choice as every instance.

A non-parametric generic is proved per instance, as today, and the report says so (`proved per instance: the signature applies 'widen' to 't'`). A generic with no constraint, such as `swap (t : type)`, is parametric: it has no concept functions, and nothing can be done with a `t` but move it.

### 3. Soundness

Two facts make an instance's proof follow from the generic proof:

1. **The instance meets the hypotheses.** For each type that meets a concept, the use check already proves every requirement contract and every law as a lemma at that type. Those lemmas are proved, or the program fails, before any instance is used. So for `t = u8` the uninterpreted `Ord.less` can be read as the `u8` `less`, and every hypothesis of the generic proof holds of it.
2. **The body is parametric.** Every operation the body applies to a value of type `t` is a requirement call, passing the value on, storing it in or loading it from a buffer, or comparing it by a concept function. The body cannot inspect the value's bits, size or type. So the instance's verification condition is the generic one with the sort read as the concrete type and each uninterpreted function read as the concrete function. This is the substitution lemma for a first-order theory: a formula valid in every model of the hypotheses is valid in the model the instance gives. The bounds and overflow goals on `usize` are the same formulas in both.

Section 2 is exactly what makes the second fact hold: it lists every way a body can see more of `t` than its concepts. The check is syntactic, made where the definition check generates the stand-in body. Anything it cannot classify falls back to per-instance proof, which is today's behaviour, so a mistake in the classifier costs build time, not soundness, as long as it only ever errs towards falling back.

Two cases need care:

- **Adapters** ([ADR 0034](0034-concepts-and-overload-resolution.md)). An instance through an adapter, `sort<t = u8, Ord = by_value>`, binds the concept's functions to the adapter's. The adapter's contracts and laws are proved at the use check like any type's, so the generic proof still applies.
- **Termination.** The generic proof proves `decreases` with the concept functions uninterpreted. A requirement function that does not terminate at some type would break fact 1, but requirement functions are ordinary functions whose own termination is proved where they are defined, or they are skipped goals there. The rule is that an instance whose type's requirement functions have skipped or unproved goals is proved per instance.

### 4. Instances, reports and the cache

- An instance of a parametric generic generates code as today, but its goals are not encoded. The report lists the generic's goals once, at the generic's lines, with the method `[generic]`. Each instance adds one line: `proved: 'lex_compare<u8>' is an instance of a generic proof [generic]`.
- `--verify-stats` gains `generic=` (goals proved at a definition) and `instances=` (instances discharged by one), so the bench shows the saving.
- **Proof cache.** A generic goal's query mentions sorts and uninterpreted functions, not widths, so it is the same query in every program that uses the generic. It is cached under its hash as any goal is ([ADR 0032](0032-parallel-sliced-cached-proving.md)). Instances need no cache entry. Editing a concept's contract or laws changes every generic query over it, which re-proves them, as it should.
- **Counterexamples.** A failed generic goal reports a model over the sort, such as `xs.[0] = t!val!0` with `Ord.less(t!val!0, t!val!1) = true`. That is an abstract counterexample: it shows which law or contract is missing. If the goal would hold at every instance in the program, the report also suggests the law that would close it. A generic that fails abstractly is not then re-proved per instance. Its definition is wrong for some model of its concepts, and the fix is a stronger constraint or law, not a narrower set of types.

### 5. Interfaces

An interface can then list a generic function with its constraints, `let lex_compare : (t : type where Ord t) -> (xs : [t]) -> (ys : [t]) -> bool ensures ...`, and its contract is checked against the definition once, by the generic proof ([ADR 0039](0039-module-and-interface-syntax.md), step 3). Importers instantiate it without re-proving it, which is what lets `Pia.Core.Order` and its successors export one generic function instead of eight stamped instances. That also needs concepts in interfaces and exported generic bodies (the inline surface, ADR 0039 step 4). This ADR supplies the proof those steps assume.

### 6. Steps

Each step is a PR with its own tests and bench numbers.

1. **Abstract encoding, reported, with no effect on instances.** Keep the definition-check function, encode stand-in types as sorts and requirement calls as uninterpreted functions with their contracts, and prove the generic's goals. Report them as `[generic]` alongside the instance goals, which are still proved. Tests: `lex_compare` over `Ord t`, `swap` over an unconstrained `t`, and the `bad` example above, which now fails with no instance. This step makes an uninstantiated generic checked at all.
2. **Instances discharged by the generic proof.** For a parametric generic whose generic goals all proved, skip encoding its instances' goals and report the instance line. Bench: `Pia.Core.Order` with the lexicographic functions restored at 8 types should cost about what one instance does now.
3. **Laws as hypotheses**, and as callable lemmas in generic bodies, with ADR 0036's relevance and fallback. `Pia.Core.Order`'s asymmetry contract on `less` becomes a law again.
4. **Fallback rules** (section 2), each with a test that a non-parametric generic is proved per instance and says why.
5. **Generic functions in interfaces**, with ADR 0039 step 3.

## Consequences

- A generic is proved once however many types use it, and an uninstantiated generic is proved at all. Library modules stop paying per type for the same proof, which is most of the cost of the generic algorithms ADR 0040 plans (`Pia.Core.Algo.*`).
- Generic proofs are about uninterpreted sorts, so they never bit-blast a value of type `t`. For bodies like `lex_compare`, whose only operation on `t` is `less`, the abstract query should be no harder than the cheapest instance's. That is expected, not measured: step 1 measures it.
- A generic that held only at the types a program happened to use, because some instance's concrete facts closed a goal, now fails at its definition with an abstract counterexample. That is the point, but it can turn a passing program into a failing one when step 1 lands. Step 1 only reports, so such generics show up before step 2 makes the generic proof the only one.
- Failed generic goals show models over sorts, which are less familiar than integer counterexamples. The report names the uninterpreted functions after the concept (`Ord.less`) to keep them readable.
- The per-instance path stays, for non-parametric bodies, so the verifier keeps both encodings.
- Laws in every query of a generic body cost what theory axioms do, and get the same relevance filtering.

## Feasibility

No code spike was made. A spike needs the three changes of step 1: keeping the definition-check function, encoding the field-less stand-in record as a sort (today ScalarizeRecords removes it, since it has no fields), and giving requirement calls their contracts at verification (today the definition-check body calls declarations without them). Those are step 1 itself, more than a spike's hour. The measurements above bound the gain: re-proving `lex_compare` at 8 types cost 8 times one instance (70.7M against about 8.8M), and a once-proof replaces the 8 with 1.
