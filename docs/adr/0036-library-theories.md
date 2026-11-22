# 36. Libraries extend the solver with theories: sorts, functions and axioms, proved consistent by a model or listed as trusted

Date: 2026-11-22

Status: Accepted (2026-11-22, with Dean's answers to its open questions below, and a catalogue of example theories added at Dean's request: [docs/theories.md](../theories.md))

## Context

Dean asked whether metaprograms could add facts and domains that reach the solver, so that a library can extend what the verifier reasons about without changes to the core compiler. His motivating case is machine learning: layers, weights, activations and residual connections, with higher-level properties such as "this network keeps its shapes consistent" or "this residual block is at most 1.5-Lipschitz" proved at the level of the network rather than of its kernels.

Pia already has most of the pieces, but not this one:

- **Spec functions and lemmas** ([PR #133](https://github.com/deanberris/pia-lang/pull/133), [docs/verifier.md](../verifier.md#spec-functions-and-lemmas)) add defined functions to the solver. Each is an uninterpreted function `F` plus its definition, guarded by its precondition, and a lemma is proved once and then assumed at its call. Everything they add is definitional, so they can never make the solver accept something false.
- **Concepts** ([ADR 0034](0034-concepts-and-overload-resolution.md)) are signatures with laws, and every instance proves the laws. An **adapter** supplies an instance.
- **Trusted items** ([ADR 0023](0023-minimal-core-self-hosted-stdlib.md)): `assume` and `addr` only in `@trusted` modules, `unsafe` calls, foreign contracts. Each is listed in its module's certificate ([ADR 0024](0024-published-proof-certificates.md)), and `piac --trust-report` lists them for a whole program.
- **Slicing and the proof cache** ([ADR 0032](0032-parallel-sliced-cached-proving.md)) keep each goal's query small and avoid re-proving.

What is missing is a way to declare a *domain*: a new sort (an abstract `layer`), functions on it that have no body (`lip`, `residual`), and facts about them (axioms). That is what SMT solvers call a theory, and Z3 takes one as declarations and quantified assertions.

The danger is plain. An axiom is a hypothesis of every query it is sent to. One wrong axiom, such as `forall x, f x = 0 && f x = 1`, makes every such query unsatisfiable, and the verifier reports every goal as proved. That breaks Pia's promise ([ADR 0004](0004-strongest-guarantee-by-default.md)) more quietly than any other feature could, so soundness decides the design.

Prior art: Why3 and Boogie let theories declare types, functions and axioms freely, and leave consistency to the author. Dafny and F\* allow `assume`-style axioms but warn, and F\* checks that an interface is realised by an implementation. Lean, Coq and Isabelle extend the logic by *definitions*, which are conservative, and they list the axioms a theorem depends on (`#print axioms`). ML module systems seal a structure with a signature, so clients see only the signature while the structure proves it can be met. Coq's `ring` and `lia` are decision procedures written in the prover and proved correct once (proof by reflection). Z3 itself offers a user propagator API, which runs arbitrary code inside the solver.

## Decision

### A theory is a signature over new sorts

A theory is a module-level item, written like a concept's signature:

```ocaml
let theory Lip = sig
  let sort layer
  let spec in_w : (f : layer) -> usize
  let spec out_w : (f : layer) -> usize
  let spec lip : (f : layer) -> real
  let spec seq : (f : layer) -> (g : layer) -> layer
  let spec residual : (f : layer) -> layer

  let axiom lip_nonneg (f : layer) ensures lip f >= 0.0
  let axiom seq_shape (f : layer) (g : layer)
    requires out_w f = in_w g
    ensures in_w (seq f g) = in_w f && out_w (seq f g) = out_w g
  let axiom seq_lip (f : layer) (g : layer)
    requires out_w f = in_w g
    ensures lip (seq f g) <= lip f * lip g
  let axiom residual_shape (f : layer)
    requires in_w f = out_w f
    ensures in_w (residual f) = in_w f && out_w (residual f) = out_w f
  let axiom residual_lip (f : layer)
    requires in_w f = out_w f
    ensures lip (residual f) <= 1.0 + lip f
  let lemma residual_twice (f : layer)
    requires in_w f = out_w f
    ensures lip (residual (residual f)) <= 2.0 + lip f
= ()
end
```

A theory can contain:

- **`let sort s`**, a new uninterpreted sort. `let sort s = t` is only an abbreviation for an existing type.
- **Abstract spec functions**, `let spec f : type` with no body. To the solver, each is an uninterpreted function. A spec function *with* a body may appear too, and it means what it means today: a definition, with `decreases` if it recurses.
- **`let axiom name params requires ... ensures ...`**: a fact, universally quantified over its parameters. To the solver it is `forall params, requires ==> ensures`.
- **`let lemma`**, proved from the theory's axioms and definitions, once, like any lemma.

Theory sorts and functions are spec-only. They can appear in contracts, spec functions, lemmas and other theories, never in code, and codegen erases them, as it erases spec functions. The spec-only types `real` and `int` (unbounded, SMT `Real` and `Int`) are available in theories for the same reason: a Lipschitz constant is a real number, not an `f32`. They already appear in the semantics of `@fp(reassoc)` ([ADR 0012](0012-floating-point-reassociation.md)), which proves `ensures` over reals. Relating float code to a real-valued theory needs an error bound in the contract, as ADR 0012's tolerance form does. That relation is out of scope here.

`theory`, `sort` and `axiom` are keywords only between `let` and the name, like `spec` and `lemma` ([grammar.md](../grammar.md#identifiers-and-keywords)).

### Metaprograms can build theories

A metaprogram can return a theory, as a concept metaprogram returns a signature:

```ocaml
let meta shape_theory (ops : [op_spec]) : theory = ...
```

So a library can describe its domain as data (a table of layer kinds, each with a shape rule) and generate the sorts, functions and axioms, and also the model below that proves them. This is how a domain reaches the solver without touching the compiler. A theory-building metaprogram must be total and pure, by the rules of [ADR 0035](0035-substitution-failure-and-total-constraints.md), because what it returns becomes hypotheses of proofs, and the hypotheses must be the same in every build. Its result is computed once per argument tuple, named after its arguments as a generic instance is (`shape_theory<...>`), and shared by every module that uses that instance.

### Soundness: every theory is either modelled or trusted

A theory with axioms has one of two statuses, recorded in its module's certificate.

**Modelled (the default, and nothing is trusted).** A model is given, in the theory's module or in another module found by the ADL rule (see [the answers below](#answers-to-the-open-questions)): a structure that picks a concrete Pia type for each sort and a spec function for each abstract function, and proves every axiom as a lemma about them.

```ocaml
let summary = type { in_w : usize; out_w : usize; lip : real where lip >= 0.0 }

let model shapes : Lip = struct
  let sort layer = summary
  let spec in_w (f : summary) : usize = f.in_w
  let spec out_w (f : summary) : usize = f.out_w
  let spec lip (f : summary) : real = f.lip
  let spec seq (f : summary) (g : summary) : summary =
    { in_w = f.in_w; out_w = g.out_w; lip = f.lip * g.lip }
  let spec residual (f : summary) : summary =
    { in_w = f.in_w; out_w = f.out_w; lip = 1.0 + f.lip }
end
```

The model is checked exactly like an adapter meeting a concept ([ADR 0034](0034-concepts-and-overload-resolution.md), "Meeting a concept"). Each sort and function has the stated type, and each axiom, with the model's definitions substituted, is proved for all values of the model's types. Here `seq_lip` becomes `f.lip * g.lip <= f.lip * g.lip`, and `lip_nonneg` follows from the refinement on `summary.lip`. A theory with a proved model is consistent: anything provable from its axioms is true in the model, so `false` cannot be. That is consistency by interpretation, the standard argument, and the solver checks it.

Then the model is **sealed**, as an ML structure is sealed by its signature. Outside the model's own body, `layer` is abstract, and a query that uses the theory gets only the sorts, the abstract functions and the axioms, never the model's definitions. That keeps clients' queries small, and it keeps them independent of the model, so the model can change without re-proving clients as long as the theory does not change.

A model proves that the axioms are consistent. It does not prove that they mean what their names suggest. `shapes` is a summary, not a semantics of neural networks: in it, a layer *is* its shape and its bound. That is the same position as any specification. A wrong axiom with a model can make a proof say less than the author meant, but it can never make the verifier accept a false goal about the program, because the program's own goals are about the program's code. How a theory's meaning connects to code is under "Connecting a theory to code" below.

**Trusted.** A theory without a model, or with a model that does not prove every axiom, is allowed only in a `@trusted` module, the same rule as `assume` ([ADR 0023](0023-minimal-core-self-hosted-stdlib.md)). Every axiom that the model does not prove is a trusted item, so it is listed in the certificate and in `--trust-report`. Trust is for facts that are true but beyond what the solver can check from a model in Pia: statements about function spaces, real analysis, or a library's external behaviour. Spectral norms are an example. The spectral norm of a matrix is at most its Frobenius norm, which is a theorem, but not one Z3 will prove over a faithful model of matrices.

Three checks make trusted axioms safer, and none of them makes them proved:

1. **Consistency check at the definition.** `piac` asks the solver whether the trusted axioms, with the base theories, are satisfiable, under the usual rlimit. `unsat` is an error that prints the unsat core: the axioms that contradict each other. `sat` with a model from Z3's model-based quantifier instantiation is recorded as a witness in the certificate. `unknown` leaves the theory trusted and unchecked, and says so. This is cheap, once per theory, and catches the usual mistakes, such as an inverted inequality or a missing precondition.
2. **Axiom use per goal.** Every axiom sent to the solver is a named assertion. When a goal is proved, the unsat core says which axioms it used, and that list is stored with the goal in the proof cache. So `piac --trust-report --why` can say "these 12 goals depend on the trusted axiom `Nn.dense_lip`", and a goal that used no trusted axiom is reported as fully proved even when its module imports a trusted theory. Unsat cores are computed only for queries that contain theory axioms.
3. **Vacuity check, opt-in.** `--check-vacuity` re-solves each proved goal that used a trusted axiom without its negated goal. If its hypotheses alone are `unsat`, the goal was proved from a contradiction, which is reported as an error. It costs one more query per such goal, so it runs in CI and in `pia-cert audit`, not in every edit.

**Importing trust is explicit.** A module that imports a theory whose certificate lists trusted axioms must say so: `import Pia.Nn.Spectral trusting`. Without `trusting`, the import is an error that lists the trusted axioms. So a library cannot grow its users' trusted base by a version bump, which fits the rule that the strongest guarantee is the default ([ADR 0004](0004-strongest-guarantee-by-default.md)). A modelled theory needs no `trusting`.

### Connecting a theory to code

Code reaches a theory through contracts, and the link is proved in the module that owns the model. A kernel module defines an abstraction function from its run-time representation to the theory's sort, inside the model's scope, and states its kernels' contracts in theory terms:

```ocaml
let spec abs (w : dense_weights) : Lip.layer
  = { in_w = w.cols; out_w = w.rows; lip = frobenius w }
```

Inside that module, `abs` unfolds into the model, so the kernels are proved against concrete definitions. Its interface publishes `abs` sealed: importers know `in_w (abs w) = w.cols` from the published contract, but not how `lip` is defined. This is data refinement, as in Dafny's and B's abstraction functions, and it is where a model's meaning matters. If the model is only a summary, as `shapes` is, then the guarantee clients get is about that summary (`lip` here is the Frobenius norm of the weights), and documentation says so. If the library wants `lip` to mean the network's true Lipschitz constant, the link between the summary and the real function is exactly the kind of fact that is a trusted axiom, and it is listed.

### Tactics and decision procedures

There are three levels, and only the first two are part of this decision.

1. **Solver strategy.** A theory, lemma or function can choose how Z3 solves its goals, with `@solver(nlsat)` or `@solver(tactic = "...")`, which becomes `(check-sat-using ...)`. This affects only speed, never soundness. The strategy is part of the proof cache key.
2. **Tactics as proof-writing metaprograms.** A tactic is a metaprogram that takes a goal (its hypotheses and conclusion as quoted terms, through a `goal` value) and returns proof steps: lemma calls, `assert`s, case splits, explicit quantifier instances and `@fuel` hints. The steps are then verified like hand-written ones, so a tactic can make a proof faster or possible but cannot make it wrong. This is the LCF approach. Proof by reflection fits in the same form. A library writes a decision procedure as a total spec function, such as `decide : shape_formula -> bool`, and proves once a lemma `decide φ ==> eval φ`. The tactic reifies the goal into a `shape_formula`, and the verifier proves `decide φ = true` by unfolding. That is a decision procedure written and proved in Pia, with nothing trusted beyond the evaluator that is already trusted.
3. **Native decision procedures** through Z3's user propagator run arbitrary code inside the solver. They are deferred. If they come, they will be `@trusted`, and the format reserves a trusted-item kind for them, unless they emit a certificate that a small checker validates.

### Hygiene and names

The names a theory declares are top-level items of its module. They are kept, not renamed, and are qualified like any other item, `Lip.lip` ([ADR 0022](0022-metaprogram-hygiene.md), rules 2 and 3). An axiom's parameters are binders, so a theory built by a quote renames them. The no-shadowing rule applies: a theory cannot declare `add`, `len` or a name already visible. Two libraries that both declare a sort `layer` declare two different sorts. A module that wants them to be the same must write a model of one in terms of the other.

In SMT-LIB, symbols are named after the module path and, for a generated theory, the instance (`|Pia.Nn.Lip.lip|`, `|shape_theory<...>.rows|`), so that queries combining two theories can never confuse their symbols.

### Concepts, laws and overloading

A theory and a concept are both signatures with facts. They differ in who proves the facts. A concept's laws are proved by every instance, and its users may assume them. A theory's axioms are proved once, by its model, or trusted. The model check reuses the adapter check unchanged.

Concepts can mention theory functions, and laws can rest on axioms: `let meta Layer (t : type) : concept = sig let abs : (x : t) -> Lip.layer ... end`. When an overload is chosen by constraint entailment or by a proved precondition (ADR 0034), and that proof uses a trusted axiom, the overload choice depends on that trust. That is recorded like any other goal's axiom use, so `--trust-report --why` shows it.

### Lowering to the `smt` dialect

A theory lowers once per module, in the verifier ([ADR 0018](0018-dialect-layering.md)), to a named fragment of `smt` operations:

- a sort to an uninterpreted sort (`!smt.sort<"Pia.Nn.Lip.layer">`);
- an abstract function to `smt.declare_fun` with an `!smt.func` type, and each use to `smt.apply_func`;
- an axiom to an `smt.forall` over its parameters, with its trigger patterns, asserted under a name;
- `real` and `int` to the SMT `Real` and `Int` sorts.

The upstream dialect has uninterpreted sorts, functions, quantifiers with patterns and `Int`. If it still lacks `Real` at our LLVM pin, the first implementation adds it in a small Pia extension that the SMT-LIB export prints, and offers it upstream. Step 1 found it lacking: `real` is written as a sort named `Real`, the Real operations as functions declared under their SMT-LIB names, and the export drops those declarations so Z3 reads them as its own ([verifier.md](../verifier.md#spec-only-int-and-real)).

Every quantified axiom needs a trigger, because an axiom without one is either ignored by E-matching or instantiated without limit. `piac` infers triggers as Z3 would (the smallest terms that mention every bound variable) and shows them in `--verify-stats`, and `@trigger(seq f g)` sets them explicitly. An axiom with no term that covers all its variables is an error at the definition.

### Build time: only the facts a goal needs

A large theory must cost nothing for goals that do not use it. That is a requirement, not an option, so it does not wait for `--slice`.

- **Relevance closure.** A query starts with its goal's own terms. An axiom is added when every function symbol in one of its triggers appears in the query, and then the closure is repeated with the symbols the new axioms bring, to a fixed point. Importing a theory costs nothing for a goal that never mentions its symbols. Leaving out an axiom only removes a hypothesis, so a proof found with the closure is a proof.
- **Fallback on failure.** If a goal is not proved with the closure, it is solved again with every axiom of every theory whose symbols it mentions, the same fallback as slicing. The counterexample comes from the larger query, so it is not spurious because of a missing axiom.
- **Sealing keeps queries small.** Clients get the axioms, never the model. A client's query does not grow with the model, and a model's proof is in its own module, proved once and cached.
- **Lemmas over re-derivation.** A theory lemma is proved once and is one fact in its users' queries, which is how a library hides an expensive chain of axiom instantiations.
- **Caching follows the facts used.** The cache key is the query, which holds only the axioms the closure added, so changing an axiom a goal never used does not invalidate the goal.
- **Parallel and measured.** Model obligations, consistency checks and vacuity checks are ordinary goals in ADR 0032's pool. Theories in the standard library join `tools/bench/corpus.txt`, so a theory whose axioms loop under E-matching shows up as a resource count regression in CI.

### Certificates

A theory is part of its module's interface ([ADR 0024](0024-published-proof-certificates.md)). Its sorts, function signatures, axioms and triggers are hashed with the interface, in the canonical form with numbered binders, so a changed axiom changes the hash and forces importers to re-prove. The certificate records each theory's status: `modelled`, with the hash of the model's proved obligations, or `trusted`, with each trusted axiom, its consistency result (`sat` with a witness, or `unknown`, since `unsat` is already an error) and whether it is a native decision procedure. Importers record the theory hashes they were proved against, and the loader checks them like any other interface. The model's body is not in the interface hash, since clients never see it.

## Worked example

The theory `Lip` and model `shapes` above are in the library `Pia.Nn`. A network builder metaprogram turns a description of a network into a term over `Lip`, and the properties of the whole network are lemmas about that term:

```ocaml
import Pia.Nn.Lip

let lemma block_bound (a : Lip.layer) (b : Lip.layer) : unit
  requires Lip.in_w a = 512 && Lip.out_w a = 512 && Lip.lip a <= 0.5
  requires Lip.in_w b = 512 && Lip.out_w b = 10 && Lip.lip b <= 2.0
  ensures Lip.in_w (Lip.seq (Lip.residual a) b) = 512
  ensures Lip.out_w (Lip.seq (Lip.residual a) b) = 10
  ensures Lip.lip (Lip.seq (Lip.residual a) b) <= 3.0
= ()
```

The goal mentions `seq`, `residual`, `in_w`, `out_w` and `lip`, so the closure brings in `residual_shape` and `residual_lip` (triggered by `residual a`), then `seq_shape` and `seq_lip` (by `seq (residual a) b`), and `lip_nonneg`. Z3 instantiates them: `residual a` is 512 to 512 with `lip <= 1.5`, so `seq` applies, and `lip <= 1.5 * lip b <= 1.5 * 2.0 = 3.0`, using `lip b >= 0` for the product. The model never enters the query, and nothing is trusted.

The shape rule catches a mistake before any kernel exists. Applying the residual to the wrong layer:

```ocaml
let lemma wrong (b : Lip.layer) : unit
  requires Lip.in_w b = 512 && Lip.out_w b = 10
  ensures Lip.lip (Lip.residual b) <= 1.0 + Lip.lip b
= ()
```

fails: the precondition of `residual_lip`, `in_w b = out_w b`, does not hold, so the axiom gives nothing, and the counterexample is a `layer` with `in_w = 512` and `out_w = 10`, whose `residual` has some unconstrained `lip`. The report names the axiom whose precondition did not hold.

The weights enter through the kernel library's abstraction function (`abs` above): a dense kernel's contract says `Lip.lip (abs w) = frobenius w`, proved in the model's module. For activations, `relu` is a layer whose `lip` is 1. In the summary model that is a definition, so it costs nothing to trust. Claiming that `lip` bounds the true Lipschitz constant of the code's function is a trusted axiom in `Pia.Nn.Spectral`, and a network proof that uses it says so in `--trust-report --why`.

## Consequences

- A library can teach the verifier a domain (shapes, units, protocols, probability, network properties) as sorts, functions and axioms, without changing the compiler, and generate it from data with a metaprogram.
- By default nothing is trusted: a theory must come with a model whose obligations the solver proves, so a library's axioms cannot make the verifier accept a false goal. Trusted axioms exist, but only in `@trusted` modules, only imported with `trusting`, checked for consistency where possible, and listed per goal.
- A model shows consistency, not meaning. Documentation has to say what a theory's functions mean, as it does for any specification, and the worked example's `lip` means "the summary's bound", not "the true Lipschitz constant".
- Clients reason over the abstract theory, so their queries stay small and do not change when a model does. The relevance closure keeps a large theory free for goals that do not use it, and its fallback keeps counterexamples honest.
- Quantified axioms bring E-matching, and with it the risk of matching loops and slow goals. Required triggers, the corpus benchmark and the rlimit contain that risk, but theory authors will need guidance on triggers in [docs/verifier.md](../verifier.md).
- Unsat cores are needed for per-goal trust, which costs some solver time on queries with theory axioms. If the benchmark shows it matters, cores can be computed only when a trusted axiom is in the query.
- New spec-only types `real` and `int`, and the keywords `theory`, `sort`, `axiom`, `model` and `trusting` in their positions.
- Implementation order, each step a PR with tests: (1) spec-only `real` and `int`, with their `smt` lowering; (2) `let theory` with sorts, abstract functions and axioms, in `@trusted` modules only, with SMT-LIB names, triggers and the relevance closure; (3) `let model`, the model check (reusing the adapter check) and sealing, which lifts the `@trusted` requirement; (4) certificate status, models found by ADL, `trusting` imports, consistency checks and per-goal axiom use in `--trust-report --why`; (5) theory-building metaprograms; (6) `@solver` strategies and tactics as proof-writing metaprograms, then proof by reflection; (7) `--check-vacuity`. Native decision procedures stay deferred.

## Answers to the open questions

Dean answered the three questions this ADR ended with when he accepted it (2026-11-22):

- **Trust is declared only in the source, and it covers a whole theory.** `import M trusting` is the only way to trust a theory, so it works the same in a file, in the REPL and in an MCP session ([ADR 0031](0031-verified-repl-and-live-environment.md)), and there is no command-line flag for it. It trusts every trusted axiom of every theory `M` exports. A theory is trusted as a whole or not at all, so there is no list of individual axioms to grant. The compiler generates the list of trusted axioms from the `trusting` imports: it is part of the importer's certificate, and `--trust-report` prints it, with `--why` naming the goals that used each axiom.
- **A model is found by the ADL rule.** A model need not be in its theory's module. As for adapters and operators ([ADR 0022](0022-metaprogram-hygiene.md), rule 5), a model of theory `T` counts where it is found in `T`'s own module or in a module the program imports explicitly. A theory with no model found that way is trusted, so importing it needs `trusting`. Importing a module that holds a proved model makes the theory modelled for that importer, with no `trusting`. Unlike adapters, two models found at once are not an ambiguity: a model is evidence that the axioms are consistent and never chooses what code means, so any one of them is enough. A module that declares a theory without a model must still be `@trusted`, and a model's certificate records the theory hash it models, so the loader can check it like any other interface hash.
- **Floats against real-valued theories get their own ADR**: [ADR 0038](0038-float-kernels-against-real-theories.md), for Dean's review. The catalogue's examples use integers, booleans and reals, so nothing in them waits on it.
