# 88. Theories cross module boundaries

Date: 2026-11-28

Status: Proposed

Amends [ADR 0036](0036-library-theories.md) (library theories) and [ADR 0039](0039-module-and-interface-syntax.md) (interfaces).

## Context

ADR 0036 says that a theory is part of its module's interface. Its sorts, abstract functions and axioms are hashed with the interface, and an importer records the theory hashes it was proved against. ADR 0036 also says that a theory built by a metaprogram is computed once per argument tuple and shared by every module that uses that instance. Neither is built. A theory today lives in the one file that declares it. `import T trusting` names a theory of the same program, and the note in ADR 0036's section on theory-building metaprograms says that sharing "waits for interfaces that carry theories".

[ADR 0087](0087-simd-vectors-as-a-library-type.md) needs both. Dean asked for a `Vector` theory in `Pia.Simd` (2026-11-28): each op's meaning is an axiom over an abstract vector, and an array model proves every axiom. `Pia.Simd` is a library, and its users' proofs must see that theory. There is one vector type per lane type and width, `simd f32 4`, `simd u8 16` and so on, so there is one theory instance per pair, and two modules that both use `simd f32 4` must agree on it. Dean ruled that theories crossing module boundaries is a must-have (2026-11-28).

## Decision

### 1. An interface exports a theory by name, and the artifact carries its declaration

An interface lists a theory as `let theory T`, as it lists a concept as `let meta C : concept`. The theory is exported with its declaration, its sorts, abstract functions, axioms and triggers, which importers need in order to prove anything. It is not exported with its model. The declaration goes into the interface artifact with the other inlined definitions (ADR 0039), so it is part of the interface hash, and a changed axiom forces importers to re-prove, as ADR 0036 says. An importer sees the theory's items qualified by the module, `Pia.Simd.Lanes.lane`. Its SMT symbols carry the same names, so two libraries' theories cannot be confused (ADR 0036).

The model stays in its module. ADR 0036 already seals it from clients, and a model in the interface would make every importer re-prove its obligations. A theory that uses a type or function its interface does not list is an error, as an inlined generic's definition is (`tests/modules/inline_errors.pia`).

### 2. The artifact records whether the theory is modelled or trusted

The exporter proves its model's obligations, and its certificate records the theory's status: `modelled`, or `trusted` with the trusted axioms (ADR 0036, section 4). A model checked in Lean by receipt (ADR 0061) counts as a model, so `Pia.Float.Exp`'s `RealExp`, whose model is Mathlib's `Real.exp`, is exported modelled. A theory with axioms but no model is `trusted`; one with no axioms is `modelled`, since it claims nothing. The interface artifact records that status next to the theory, as `let theory T @modelled` or `let theory T @trusted`. The importer follows ADR 0036's rule:

- A modelled theory needs no `trusting`. Its axioms are facts that a model proved, and the loader checks that the certificate of the module the program links says the same.
- A trusted theory needs `import M.I trusting`. Without it, the import is an error that lists the trusted axioms. With it, the axioms are trusted items in the importer's `--trust-report`.

### 3. A theory built by an exported metaprogram is built in the importer, model and all

A metaprogram that returns a theory and its model, such as the prelude's `machine`, is exported with its definition, as every metaprogram is (ADR 0039). An importer that applies it, `let theory T = lanes_theory f32 4`, gets the theory and the model, and proves the model's obligations itself. They are lemmas, cached by the proof cache like any other. So an instance that only an importer uses is modelled there, and nothing is trusted.

The instance is named after the metaprogram and its arguments, `lanes_theory<f32, 4>`, wherever it is built. Its items and SMT symbols carry that name, and two modules that build the same instance build the same items, so their proofs combine.

For a generic type, the instance is built where the type's instance is formed. A generic type may name a theory-building metaprogram in a `with` clause, `let simd = let (t : type) (k : usize) => type { lanes : [t; k] } with lanes_theory t k`. Each instance of the type then builds the theory instance for its arguments, once per program, and functions generic over the type see `lanes_theory<t, k>`'s items for their instance's `t` and `k`. That is how `Pia.Simd` gives every `simd t k` its theory without a list of instances.

### 4. Abstraction functions are exported sealed

A library links its run-time type to the theory's sort with an abstraction function proved in the model's scope (ADR 0036, section 5): `Pia.Simd`'s `view : (v : simd t k) -> Lanes.vec` for each instance, with `lane (view v) i = v.lanes.[i]`. It is exported as an opaque spec function (ADR 0063), so importers get its contract and never its body. The ops' contracts are stated through it: `ensures view result = Lanes.plus (view a) (view b)`.

## Consequences

- A library can describe its domain as a theory and let its users prove against it. That is what ADR 0036 promised and what `Pia.Simd`'s `Vector` theory needs.
- Nothing becomes trusted by crossing a module boundary. A modelled theory stays modelled for importers, and a generated instance is modelled where it is built.
- Interfaces grow by the theory's declaration, which is small next to the model.
- Each program that uses a generated instance proves its model once, and the proof cache shares the proof between builds.

## Implementation order

Each step is one PR with tests, docs and skill changes.

1. **Exported theories** (sections 1 and 2): `let theory T` in an interface, the declaration and status in the artifact, qualified items in the importer, `trusting` across modules, and the interface hash. Tested in `tests/modules`, with a modelled theory, a trusted one with and without `trusting`, and an axiom change that changes the hash.
2. **Generated instances across modules** (section 3): an exported theory-building metaprogram applied by an importer, instance names `gen<args>`, and `with` on a generic type. Tested by two modules that build the same instance, and one that builds it for a generic type's instances.
3. **`Pia.Simd`'s `Vector` theory** (ADR 0087): `lanes_theory t k`, `view`, and the ops' contracts through it.

## Open questions

None. The status marker in section 2 follows ADR 0036's certificate status, and the `with` clause in section 3 is the smallest syntax that ties an instance to its type.
