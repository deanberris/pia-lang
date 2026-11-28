# Feature index

Every feature `piac` builds today, with the page that explains it and a working example: a file in [`tests/verify`](../tests/verify/) that `bazel test //tests/verify:<name>_test` proves, and whose expected report sits in its comments. To see a feature at work, read its example, or run `piac --verify` on it. [Status](status.md) says what is built and what comes next; [the standard library](library.md) lists the modules written with these features.

`tools/docs/check.py` fails a pull request that adds a feature test without a line here.

## Values and types

| Feature | Explained in | Examples |
| --- | --- | --- |
| Bounded integers, range types and overflow modes | [tour](tour.md#integers), [design](design.md#primitive-types-and-overflow) | [overflow](../tests/verify/overflow.pia) |
| Digit separators, `min t` and `max t` | [tour](tour.md#integers), [grammar](grammar.md#literals) | [digit_separators](../tests/verify/digit_separators.pia), [type_bounds](../tests/verify/type_bounds.pia) |
| Bit operators and the builtins `clz`, `ctz`, `popcount`, `bswap`, `rotl`, `rotr` | [verifier](verifier.md#intervals-first), [Pia.Core.Bit](library.md#core) | [bits](../tests/verify/bits.pia), [bit_counts](../tests/verify/bit_counts.pia) |
| No shadowing, and primed names such as `x'` | [tour](tour.md#no-shadowing) | [primes](../tests/verify/primes.pia) |
| Arrays and slices, constant tables | [tour](tour.md#arrays-and-slices) | [slices](../tests/verify/slices.pia), [local_arrays](../tests/verify/local_arrays.pia), [array_results](../tests/verify/array_results.pia), [consts](../tests/verify/consts.pia), [const_array_views](../tests/verify/const_array_views.pia) |
| Records, and buffers of records | [tour](tour.md#records) | [records](../tests/verify/records.pia), [record_buffers](../tests/verify/record_buffers.pia), [slice_aggregates](../tests/verify/slice_aggregates.pia) |
| Variants and `match`, record payloads | [tour](tour.md#variants-and-match) | [variants](../tests/verify/variants.pia), [record_payloads](../tests/verify/record_payloads.pia) |
| Type aliases, `let byte = u8` | [tour](tour.md#records) | [type_aliases](../tests/verify/type_aliases.pia) |
| Distinct types, `type u32`, and their derives | [tour](tour.md#records), [ADR 0064](adr/0064-distinct-types.md) | [distinct_types](../tests/verify/distinct_types.pia), [distinct_derives](../tests/verify/distinct_derives.pia) |
| Parameter modifiers, `inout` and `old` | [tour](tour.md#parameter-modifiers) | [inout_values](../tests/verify/inout_values.pia), [old_calls](../tests/verify/old_calls.pia) |
| Recursive types, `let rec` variants | [verifier](verifier.md#recursive-types) | [rec_types](../tests/verify/rec_types.pia), [rec_aliasing](../tests/verify/rec_aliasing.pia), [rec_fill](../tests/verify/rec_fill.pia) |
| Floats, `f32` and `f64` | [tour](tour.md#floats), [verifier](verifier.md#floats) | [floats](../tests/verify/floats.pia) |

## Contracts and proofs

| Feature | Explained in | Examples |
| --- | --- | --- |
| `requires`, `ensures` and `assert`, and calls proved from contracts | [tour](tour.md#contracts), [how verification works](verification.md#contracts-are-the-interface) | [contracts](../tests/verify/contracts.pia), [callee_exact](../tests/verify/callee_exact.pia) |
| Contracts are exact mathematics | [verifier](verifier.md#goals) | [spec_exact](../tests/verify/spec_exact.pia), [contract_equality](../tests/verify/contract_equality.pia), [contract_guards](../tests/verify/contract_guards.pia) |
| Goals proved by intervals, before Z3 | [verifier](verifier.md#intervals-first) | [intervals](../tests/verify/intervals.pia) |
| How products are encoded, exact division facts, int-blasting | [verifier](verifier.md#encoding), [ADR 0066](adr/0066-int-blasting-for-nonlinear-goals.md) | [widths](../tests/verify/widths.pia), [division_facts](../tests/verify/division_facts.pia), [int_blast](../tests/verify/int_blast.pia) |
| Loop invariants and `decreases` | [verifier](verifier.md#loops), [verifier](verifier.md#termination) | [loops](../tests/verify/loops.pia), [int_measures](../tests/verify/int_measures.pia) 
| Mutual recursion: a `decreases` goal at each call within a cycle of functions | [verifier](verifier.md#termination) | [mutual_recursion](../tests/verify/mutual_recursion.pia) |
| Spec functions and lemmas | [verifier](verifier.md#spec-functions-and-lemmas) | [specs](../tests/verify/specs.pia), [pure_calls](../tests/verify/pure_calls.pia), [fuel_counterexamples](../tests/verify/fuel_counterexamples.pia) |
| Opaque spec functions, `@opaque` and `with f` | [verifier](verifier.md#spec-functions-and-lemmas), [ADR 0063](adr/0063-opaque-spec-functions.md) | [opaque](../tests/verify/opaque.pia) |
| Frames, `reads xs.[lo .. hi]` | [verifier](verifier.md#spread) | [frames](../tests/verify/frames.pia) |
| Lemmas proved in Lean, `by lean`, `--emit=lean`, receipts in certificates and `--trust-report` | [verifier](verifier.md#spec-functions-and-lemmas), [ADR 0061](adr/0061-lean-proved-facts.md) | [by_lean](../tests/verify/by_lean.pia), [sums](../tests/lean/sums.pia), [native_trusted](../tests/lean/native_trusted.pia) |
| Spec-only `int` and `real` | [verifier](verifier.md#spec-only-int-and-real) | [reals](../tests/verify/reals.pia) |
| Spec state: `let spec` locals and `spec` fields | [verifier](verifier.md#spec-state), [ADR 0058](adr/0058-spec-buffers.md) | [spec_locals](../tests/verify/spec_locals.pia), [spec_fields](../tests/verify/spec_fields.pia), [spec_buffers](../tests/verify/spec_buffers.pia) |
| Cost bounds, `costs iterations` and `costs calls` | [tour](tour.md#cost-bounds), [verifier](verifier.md#cost-bounds), [ADR 0062](adr/0062-cost-bounds-in-contracts.md) | [costs](../tests/verify/costs.pia) |
| `assume`, `@trusted` and `--trust-report --why` | [how verification works](verification.md), [ADR 0023](adr/0023-minimal-core-self-hosted-stdlib.md) | [assumes](../tests/verify/assumes.pia) |
| `--check-vacuity` | [verifier](verifier.md#theories) | [vacuity](../tests/verify/vacuity.pia) |
| Parallel, sliced and cached proving | [verifier](verifier.md#parallel-sliced-and-cached-proving) | [parallel](../tests/verify/parallel.pia) |
| Solver strategies `@solver` and tactics `@by` | [verifier](verifier.md#solver-strategies-and-tactics) | [solver](../tests/verify/solver.pia), [tactics](../tests/verify/tactics.pia) |
| `--emit=mlir` with proved ops marked | [getting started](getting-started.md#piac-at-a-glance) | [emit](../tests/verify/emit.pia) |

## Theories

| Feature | Explained in | Examples |
| --- | --- | --- |
| Theories: sorts, abstract functions, axioms and triggers | [theories](theories.md), [verifier](verifier.md#theories) | [theory_lip](../tests/verify/theory_lip.pia), [theory_closure](../tests/verify/theory_closure.pia) |
| Models, which prove a theory's axioms | [theories](theories.md#writing-a-theory) | [models](../tests/verify/models.pia), [model_check](../tests/verify/model_check.pia) |
| Consistency of trusted theories | [verifier](verifier.md#theories) | [trust_checks](../tests/verify/trust_checks.pia) |
| Theories built by metaprograms, such as `machine` | [theories](theories.md#state-machines), [meta](meta.md#theory-building-metaprograms) | [machine](../tests/verify/machine.pia) |
| The target as a theory, and `@target(m)` items | [theories](theories.md#the-target), [ADR 0049](adr/0049-targets-are-theories.md) | [target](../tests/verify/target.pia), [target_items](../tests/verify/target_items.pia), [target_theory](../tests/verify/target_theory.pia) |

## Generics, overloading and metaprograms

| Feature | Explained in | Examples |
| --- | --- | --- |
| Generic functions and types | [tour](tour.md#generics) | [generic_functions](../tests/verify/generic_functions.pia), [generic_types](../tests/verify/generic_types.pia) |
| Value parameters on types, `block u8 4` | [tour](tour.md#generics), [ADR 0074](adr/0074-library-types-tensors.md) | [value_params](../tests/verify/value_params.pia), [shapes](../tests/verify/shapes.pia) |
| `@lower` on a type: a record's MLIR type, a memref view of its buffer | [codegen](codegen.md#lowerings-written-in-pia), [ADR 0074](adr/0074-library-types-tensors.md) | [lower_type](../tests/codegen/lower_type.pia) |
| Generic bodies proved once | [verifier](verifier.md#generic-functions), [ADR 0043](adr/0043-generic-definitions-proved-once.md) | [generic_proofs](../tests/verify/generic_proofs.pia) |
| Concepts with laws, and adapters | [tour](tour.md#concepts), [ADR 0034](adr/0034-concepts-and-overload-resolution.md) | [concepts](../tests/verify/concepts.pia), [adapters](../tests/verify/adapters.pia), [generic_meets_concept](../tests/verify/generic_meets_concept.pia) |
| Overloading, ranked by constraints and chosen by precondition | [verifier](verifier.md#choosing-overloads-by-precondition), [ADR 0034](adr/0034-concepts-and-overload-resolution.md) | [overloads](../tests/verify/overloads.pia), [concept_ranking](../tests/verify/concept_ranking.pia), [precondition_overloads](../tests/verify/precondition_overloads.pia) |
| Type-level metaprograms, `match` on types, substitution failure | [meta](meta.md#type-level-metaprograms), [ADR 0035](adr/0035-substitution-failure-and-total-constraints.md) | [type_functions](../tests/verify/type_functions.pia), [type_match](../tests/verify/type_match.pia), [total_metaprograms](../tests/verify/total_metaprograms.pia), [soft_failure](../tests/verify/soft_failure.pia) |
| Tests generated from contracts: `Pia.Test.Gen`'s `cases`, `@case`, and specification failures | [meta](meta.md#tests-from-contracts), [ADR 0056](adr/0056-tests-generated-from-contracts-and-theories.md) | [test_gen](../tests/std/test_gen.pia), [test_gen_spec](../tests/std/Inputs/test_gen_spec.pia) |
| Lambdas and function values | [tour](tour.md#function-values), [ADR 0044](adr/0044-function-values-and-lambdas.md) | [lambda_find](../tests/verify/lambda_find.pia), [lambda_generic](../tests/verify/lambda_generic.pia), [lambda_generic_forms](../tests/verify/lambda_generic_forms.pia), [lambda_named](../tests/verify/lambda_named.pia), [lambda_overloads](../tests/verify/lambda_overloads.pia) |
| Contracts on function types | [verifier](verifier.md#higher-order-functions-proved-once) | [lambda_arrow_contract](../tests/verify/lambda_arrow_contract.pia), [lambda_requires](../tests/verify/lambda_requires.pia) |
| Captures, partial application and closures as results | [tour](tour.md#function-values) | [lambda_captures](../tests/verify/lambda_captures.pia), [lambda_results](../tests/verify/lambda_results.pia) |
| Function references: `let h : (x : u8) -> u8 requires ... = succ`, and `mutable` ones rebound with `<-` and called indirectly | [tour](tour.md#function-values), [ADR 0071](adr/0071-function-references.md) | [fn_references](../tests/verify/fn_references.pia), [fn_references_mutable](../tests/verify/fn_references_mutable.pia) |
| Function reference fields: `type { f : (x : u8) -> u8 requires ...; ... }`, stored and rebound with `<-`, and buffers of them as tables called indirectly | [tour](tour.md#function-values), [codegen](codegen.md), [ADR 0071](adr/0071-function-references.md) | [fn_reference_fields](../tests/verify/fn_reference_fields.pia) |
| Function objects, any type with an `apply` | [tour](tour.md#function-values) | [function_object](../tests/verify/function_object.pia) |

## Errors, resources and memory

| Feature | Explained in | Examples |
| --- | --- | --- |
| Error sets, `?` and `handle` | [stdlib](stdlib.md#errors-and-scope-cleanup), [ADR 0028](adr/0028-error-propagation-and-cleanup.md) | [error_sets](../tests/verify/error_sets.pia), [error_set_unions](../tests/verify/error_set_unions.pia), [handlers](../tests/verify/handlers.pia) |
| An open case in a closed error set: a constructor carrying `box c` | [stdlib](stdlib.md#errors-and-scope-cleanup), [ADR 0046](adr/0046-box-over-a-type-or-a-concept.md#note-2026-11-27-a-box-over-a-concept-as-an-error-payload) | [box_error_payload](../tests/verify/box_error_payload.pia) |
| `defer` | [stdlib](stdlib.md#errors-and-scope-cleanup) | [defer](../tests/verify/defer.pia) |
| Foreign functions, contracted or `unsafe`, and `unsafe view` | [codegen](codegen.md#foreign-functions) | [ffi](../tests/verify/ffi.pia), [views](../tests/verify/views.pia) |
| Allocators: bump, arenas, pools and size classes | [stdlib](stdlib.md#7-linear-resources-and-memory), [theories](theories.md#allocators), [Pia.Mem](library.md#memory) | [bump](../tests/verify/bump.pia), [arena](../tests/verify/arena.pia), [pool](../tests/verify/pool.pia), [pool_alloc](../tests/verify/pool_alloc.pia), [pool_owner_errors](../tests/verify/pool_owner_errors.pia), [size_classes](../tests/verify/size_classes.pia) |
| Growable vectors | [stdlib](stdlib.md#the-litmus-test-a-proved-growable-array), [Pia.Mem](library.md#memory) | [vec_bump](../tests/verify/vec_bump.pia), [vec_generic](../tests/verify/vec_generic.pia), [vec_region](../tests/verify/vec_region.pia), [vec_allocator](../tests/verify/vec_allocator.pia) |
| `box t`, and `box` over a concept | [Pia.Mem](library.md#memory), [ADR 0046](adr/0046-box-over-a-type-or-a-concept.md) | [box](../tests/verify/box.pia), [box_errors](../tests/verify/box_errors.pia), [box_concept](../tests/verify/box_concept.pia) |
| Buffers whose elements hold slices or boxes, `@linear` | [ADR 0048](adr/0048-buffers-whose-elements-hold-slices.md) | [slice_buffers](../tests/verify/slice_buffers.pia), [vec_boxes](../tests/verify/vec_boxes.pia) |
| Atomics | [codegen](codegen.md#atomics), [ADR 0052](adr/0052-atomics.md) | [atomics](../tests/verify/atomics.pia) |

## Modules and concurrency

| Feature | Explained in | Examples |
| --- | --- | --- |
| Modules and interfaces, met by proof | [getting started](getting-started.md), [ADR 0039](adr/0039-module-and-interface-syntax.md) | [modules](../tests/verify/modules.pia) |
| A definition with no contract takes its interface's, so a contract is written once | [getting started](getting-started.md#contracts-written-once), [ADR 0077](adr/0077-definitions-inherit-interface-contracts.md) | [inherited_contracts](../tests/verify/inherited_contracts.pia) |
| `spread`, a parallel loop whose iterations own their cells, and `@owns` | [tour](tour.md#parallel-loops), [verifier](verifier.md#spread), [ADR 0060](adr/0060-spread-v0-ownership-and-runtime.md) | [spread](../tests/verify/spread.pia), [spread_ensures](../tests/verify/spread_ensures.pia), [spread_frame](../tests/verify/spread_frame.pia) |
| `@place(gpu)` on a `spread`, a Metal kernel, and on a `for`, a sequence of kernels in one command buffer | [D8 on the GPU](placed.pia.md), [the pull step on the GPU](pull_gpu.pia.md), [ADR 0068](adr/0068-gpu-compute-through-spirv-and-metal.md) | [gpu_sequence](../tests/verify/gpu_sequence.pia) |

## Demos

| Demo | Explained in | Examples |
| --- | --- | --- |
| Sediment transport in fixed point: conservation, the height order, the whole step | [sediment transport](sediment.pia.md), [ADR 0055](adr/0055-sediment-transport-in-fixed-point.md) | [sediment](../tests/verify/sediment.pia), [sediment_order](../tests/verify/sediment_order.pia), [sediment_transport](../tests/verify/sediment_transport.pia) |
