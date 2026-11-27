# 61. Lean proves the facts Z3 cannot: lemmas and theory models are proved in Lean against statements piac generates, recorded in certificates by statement hash, and checked outside the edit loop; cost bounds are proved by Z3, and their asymptotics in Lean

Date: 2026-11-24

Status: Accepted (2026-11-24, with Dean's answers below; the Z3 half of cost proofs moved to [ADR 0062](0062-cost-bounds-in-contracts.md), which goes first)

## Context

Dean asked whether Lean could take part in the proof pipeline, for claims such as complexity bounds and general theorems that Z3 handles poorly.

Pia proves code with intervals and Z3 ([ADR 0011](0011-mlir-and-z3-implementation.md)). Z3 is a decision procedure with quantifier heuristics. It is very good at the goals code raises: bounds, overflow, frames, loop invariants, the instances of a theory's axioms. It is poor at three kinds of claim, and Pia already meets all three:

1. **Induction beyond one step.** Z3 does no induction. Pia's answer is a recursive `lemma` with `decreases`, one step per unfolding ([verifier.md](../verifier.md#spec-functions-and-lemmas)). That works for a sum or a count. It does not work for a proof that needs a strengthened induction hypothesis, a lemma about a closed form, or several nested inductions, such as the suffix reversal of `next_permutation`, which costs 482M on one invariant and is parked ([cpp-std.md](../cpp-std.md)).
2. **Mathematics.** Real analysis, linear algebra and asymptotics are outside what Z3 decides. [ADR 0036](0036-library-theories.md) names the spectral norm bound as its example of a fact that is true but has to be *trusted*, because Z3 will not prove it over a faithful model of matrices. [ADR 0038](0038-float-kernels-against-real-theories.md) needs rounding-error bounds and, later, Taylor remainders. Today each such fact becomes a trusted axiom.
3. **Complexity.** Pia has no cost proofs. [ADR 0040](0040-cpp23-standard-library-in-pia.md) documents C++'s complexity clauses and does not prove them, and [ADR 0056](0056-tests-generated-from-contracts-and-theories.md) checks them by fitting benchmarks. "At most `log2 n + 1` comparisons" is a claim about every `n`, and `O(n log n)` is a limit statement, which no SMT solver handles.

Lean 4 with Mathlib handles all three. It has induction of every kind, a large library of analysis, algebra and asymptotics (`Asymptotics.IsBigO`, and a formalised Akra–Bazzi theorem in `Mathlib.Computability.AkraBazzi`), and a small kernel that checks every proof. It is also slow to set up (a toolchain and gigabytes of Mathlib), and its proofs are written by people or agents, not found automatically. So the question is where it fits without making the edit loop slower, without widening the trusted base silently, and without a second semantics of Pia to keep in step.

### Prior art

| System | What it does | What Pia takes |
| --- | --- | --- |
| [Lean-SMT](https://arxiv.org/abs/2505.15796) (Mohamed, Mascarenhas, Barbosa, Tinelli et al., 2025) | An `smt` tactic: Lean goal to SMT-LIB, cvc5 solves it, and cvc5's proof is rebuilt in Lean and checked by the kernel. About 200 of cvc5's proof rules are reconstructed. | The mapping from SMT-LIB sorts to Lean types (bit-vectors to `BitVec n`, `Int` to `ℤ`, `Real` to `ℝ`, uninterpreted functions to variables) is worked out and tested. It is the same mapping, run in the other direction, that piac needs. |
| [Lean-auto](https://github.com/leanprover-community/lean-auto) (Qian et al.) | Translates Lean goals into first-order logic for SMT solvers and ATPs, and calls them as hammers. | Agents writing Lean proofs of Pia's statements can use it, and Lean-SMT, as automation, so most easy goals need no hand proof. |
| [Loom and Velvet](https://ilyasergey.net/assets/pdf/papers/velvet-cav26.pdf) (Verse lab, 2025–26) | A Dafny-style verifier embedded in Lean: VCs go to `grind`, then to an SMT solver through Lean-auto, and the rest are proved by hand in Lean. | The same split between automatic and interactive proof, but inside Lean. Pia keeps Z3 as the main prover and uses Lean only where Z3 fails, so its edit loop does not depend on Lean. |
| [Aeneas](https://github.com/AeneasVerif/aeneas) (Ho, Protzenko) | Translates safe Rust into pure Lean functions, using the borrow checker to make the translation functional, and proofs of the code are in Lean. | A warning about scope. Translating *code* means a second semantics of the language, which must agree with codegen. Pia translates only spec-level statements, which already have a pure, total meaning. |
| Dafny, F\*, Why3 | Automatic provers with escape hatches: Why3 sends a goal to Coq or Isabelle when SMT fails, and the goal is printed in the target's logic. | Why3's model, with one change. Why3 exports raw goals, which change on every edit. Pia exports *lemmas*, whose statements are stable. |
| Isabelle's Sledgehammer | ATPs and SMT find proofs, and Isabelle reconstructs them. | The reverse direction (SMT inside the proof assistant). Pia does not need it to use Lean, but it is the route to re-checkable certificates (below). |
| CompCert, CakeML | The compiler itself is proved in a proof assistant. | Out of scope. Pia's compiler and VC generator stay trusted, as they are today, and nothing here changes that. |
| RAML (Hoffmann), time credits (Charguéraud and Pottier), Liquid Haskell's resource analysis (Handley, Vazou, Hutton), calf (Niu, Sterling, Grodin, Harper) | Cost as a resource in the logic: a counter or credits consumed by each step, bounded in the specification. RAML infers polynomial bounds by linear programming. | Cost as a ghost counter in contracts, proved by Z3 like any other contract. The asymptotic claims about the bound are proved in Lean. |

## Decision

Lean is a second prover for facts at the level of specifications: lemmas, models of theories, and closed forms and asymptotics of cost bounds. It never sees code, and it never runs while a program is verified. Four parts.

### 1. A lemma can be proved in Lean

A `lemma` (or a theory's `lemma`) can name a Lean theorem instead of a body:

```ocaml
let lemma reverse_suffix (xs : [u8]) (k : usize) : unit
  requires k < len xs && descending xs (k + 1) (len xs)
  ensures ascending (reversed xs (k + 1) (len xs)) 0 (len xs - k - 1)
= by lean Pia.Core.Algo.Permutation.reverse_suffix
```

`piac --emit-lean M` writes one Lean file per module, `M/Statements.lean`, with every spec function the lemmas mention, translated to Lean definitions, and every `by lean` lemma's statement as a `def ... : Prop`. The author, or an agent, writes the proof in a separate file:

```lean
import Pia.Core.Algo.Permutation.Statements

theorem Pia.Core.Algo.Permutation.reverse_suffix :
    Pia.Core.Algo.Permutation.Statements.reverse_suffix := by
  intro xs k hk hdesc
  ...
```

Lean checks that the theorem's type is the generated statement, so the author cannot prove a different statement by mistake. In Pia the lemma is then an ordinary lemma: its callers prove its precondition and assume its postcondition, and Z3 never sees its proof.

Lemmas, not raw goals, are the unit, because their statements are stable. A goal's SMT query changes with every edit to the function around it, with slicing and with the relevance closure, so a Lean proof of a raw query would go stale on every edit. A lemma's statement changes only when its author changes it. For exploration, `piac --emit-lean --goal file.pia:line` still prints one failed goal as a Lean statement, with its hypotheses, to help an author decide what lemma to write.

**The translation.** Only spec-level terms are translated, and they are already pure and total. Each construct maps to Lean as its SMT encoding does ([verifier.md](../verifier.md#encoding)), so the Lean statement means what Z3 would have been asked:

| Pia | Lean |
| --- | --- |
| `bool` | `Prop` in statements, `Bool` in values |
| `int`, `real` | `ℤ`, `ℝ` (Mathlib) |
| `u8` ... `u64`, `usize`, `i8` ... `i64` | `BitVec n`, with Pia's operations, which are guarded against overflow where Pia's are |
| slices `[t]` and spec buffers | a length and a function from indices, the SMT array encoding |
| records, sums, `let rec` sums | `structure`, `inductive` |
| spec functions with `decreases m` | Lean definitions with `termination_by m` and the same measure |
| a theory's sorts and abstract functions | fields of a Lean `structure`, with the axioms as fields too (below) |

The places where the two logics differ are where translation bugs hide, so each is a rule with a test. SMT's `x / 0` is an unspecified value and Lean's is `0`, so division and `mod` are translated as guarded uninterpreted functions unless a nonzero divisor is in scope. Pia's partial spec functions (with `requires`) become Lean functions with the precondition as an argument. Every translated construct has a round-trip test: a lemma proved in Pia by Z3 is emitted, proved in Lean by `decide`, `omega` or `grind`, and a lemma that is false in Pia must be unprovable in Lean (its negation is proved).

### 2. A theory can be modelled in Lean

An [ADR 0036](0036-library-theories.md) theory is either modelled (consistent, proved by a model in Pia) or trusted. A model in Lean is a third way to give one:

```lean
-- Generated from `let theory Lip = sig ... end`
structure Pia.Nn.Lip (layer : Type) where
  in_w : layer → ℕ
  lip : layer → ℝ
  seq : layer → layer → layer
  ...
  lip_nonneg : ∀ f, 0 ≤ lip f
  seq_lip : ∀ f g, out_w f = in_w g → lip (seq f g) ≤ lip f * lip g
  ...

-- Written by the library: the true Lipschitz constant of linear maps
noncomputable def Pia.Nn.Spectral.model : Pia.Nn.Lip LinearLayer := { ... }
```

`let model spectral : Lip = by lean Pia.Nn.Spectral.model` names it. The model proves the theory consistent, as a Pia model does, so the theory is *modelled*, not trusted, and importers do not write `trusting`. A Lean model can do what a Pia model cannot: it can give the functions their real meaning (the operator norm of a matrix over `ℝ`, not a summary record), so the theory's axioms are true of what the names say, not only consistent. That turns ADR 0036's example trusted axiom, "the spectral norm is at most the Frobenius norm", into a proved fact.

A theory lemma proved in Lean is proved from the structure's axiom fields only, for every instance, so it holds in every model and does not depend on which model the importer found.

### 3. Cost bounds are proved by Z3; their closed forms and asymptotics in Lean

Most complexity clauses are exact bounds, not asymptotics, and Z3 can prove exact bounds if cost is part of the contract. So cost comes in two layers.

**Cost in contracts, proved by Z3.** A function bounds what it spends on a named counter with a `costs c <= e` clause, proved by Z3 like any other contract, with the spec-only value `spent c` bounded by loop invariants. That design is its own decision, [ADR 0062](0062-cost-bounds-in-contracts.md), and it needs no Lean. This section is only about what Lean adds to it.

**Closed forms and asymptotics in Lean.** Some bounds are recurrences: a divide-and-conquer function's `costs` is a recursive spec function `t n = 2 * t (n / 2) + n`, which Z3 can check step by step but cannot solve. Two kinds of lemma about such a `t` are proved in Lean by part 1 of this ADR:

- a **closed form**, `t n <= 2 * n * log2 n + n`, which callers then use in their own cost clauses, so Z3 never sees the recurrence;
- an **asymptotic claim**, written with the spec-only form `t in O(fun n => n * log2 n)`, translated to Mathlib's `IsBigO atTop`. Mathlib's Akra–Bazzi theorem covers most divide-and-conquer recurrences. An asymptotic claim is documentation that is proved: no Pia goal can use it, since contracts are about concrete runs, but the interface publishes it, and the C++ library's complexity clauses become proved facts instead of comments.

Amortised bounds (a `vec` push, union–find) use a potential as a spec function over the data structure's model, as in Charguéraud and Pottier's work: `costs calls <= 1 + potential (old v) - potential v`. Z3 proves the per-operation bound (ADR 0062), and Lean proves any closed form of the potential that needs induction.

### 4. Certificates and trust

A Lean-proved fact is neither proved by Z3 nor trusted in ADR 0036's sense. It is a third status, `lean`, recorded per item in its module's certificate ([ADR 0024](0024-published-proof-certificates.md)):

```
lean Pia.Core.Algo.Permutation.reverse_suffix
  statement <SHA-256 of the canonical Pia statement>
  lean-statement <SHA-256 of the generated Lean statement>
  toolchain leanprover/lean4:v4.x.y
  mathlib <commit>
  axioms propext Classical.choice Quot.sound
```

- **The statement hash** is over the lemma's canonical form, the same serialisation the interface hash uses, so a changed statement invalidates the proof, and a proof cannot be attached to another statement.
- **The axioms** are what Lean's `#print axioms` reports for the theorem. The standard three (`propext`, `Classical.choice`, `Quot.sound`) are allowed. `sorryAx` is an error. `Lean.ofReduceBool` (from `native_decide`, which trusts Lean's compiler) is allowed only in a `@trusted` module and is listed as a trusted item, under the same rules as `assume`.
- **`--trust-report`** lists Lean facts in their own section, with `--why` naming the goals that used each one, exactly as it does for trusted axioms. What they rest on is stated plainly: Lean's kernel, Mathlib's definitions, and piac's translation of the statement. The translation is the new trusted component, and it is small: it covers spec terms only.
- **The loader never runs Lean**, as it never runs Z3. `pia-cert audit` can re-check a Lean fact by regenerating the statement and replaying the proof with Lean, or with an independent kernel such as `lean4checker`.

Importing a module whose certificate lists Lean facts needs no `trusting`, because nothing in it is unproved.

### Where Lean runs, and what it costs

Lean never runs inside `piac --verify`, the REPL or the language server. piac reads a **receipt** for each `by lean` item: a small file with the statement hash, the Lean statement hash, the toolchain, the Mathlib commit and the axioms, as in the certificate. A receipt whose statement hash does not match the current statement is a failed goal, "the Lean proof of `reverse_suffix` is for another statement; run `bazel build //lib:lean_proofs`", and the goal is reported like any unproved goal. So an edit costs nothing more than reading a receipt, and an edit that changes a Lean-proved statement fails fast and says why.

Receipts are produced by a Bazel rule, `pia_lean_proof`, which runs `piac --emit-lean`, then `lake build` over the proof files, then `#print axioms`, and writes the receipt. The rule is in a separate target, like the proof benchmark, so ordinary builds and tests use the receipts from the Bazel cache and only a change to a Lean file or a Lean-proved statement runs Lean. Receipts are build outputs, never checked in, so a receipt always comes from a real Lean run.

The costs, to be measured in step 1 and tracked by the build-time benchmark ([ADR 0032](0032-parallel-sliced-cached-proving.md)):

- **The toolchain** is one download of a few hundred megabytes per Lean version, fetched by Bazel from Lean's release assets as a pinned, hashed archive.
- **Mathlib** is the large part: several gigabytes of compiled `.olean` files. Building it from source takes hours, so Bazel fetches the prebuilt cache for the pinned commit. Proof files import only the Mathlib modules they need, which keeps each `lake build` to seconds or minutes after the cache is warm. Proofs that need no Mathlib (most induction lemmas over lists and bit-vectors, which Lean's core library and `omega`, `grind` and `bv_decide` handle) use a target without it.
- **Pinning.** Lean and Mathlib change often, and an upgrade can break proofs. The toolchain and Mathlib commit are pinned in `MODULE.bazel`, upgraded deliberately in their own PR, and every receipt names them.

Lean proofs are checked in the Linux CI job of [ADR 0049](0049-targets-are-theories.md) and on the iMac. They are independent of the target, so they are checked once, not per target.

### What Lean is not used for

- **Not for code.** Lean never sees a function body, so there is no second semantics of Pia's code to keep in step with codegen, as there would be with an Aeneas-style translation.
- **Not instead of Z3.** A goal goes to Lean only through a lemma that its author chose to prove there. The default remains "every goal proved automatically, or a compile error".
- **Not, yet, as the checker of Z3's proofs.** Lean-SMT shows that SMT proofs can be rebuilt in Lean, which would let certificates carry proofs that a consumer re-checks without trusting Z3 (the proof objects [docs/abi.md](../abi.md) reserves room for). Its reconstruction covers cvc5, not Z3, and a fraction of the rules. It is a later decision.

## Consequences

- Facts that are trusted today, such as ADR 0036's spectral norm bound, can become proved, and the theory can mean what its names say, not only be consistent.
- Lemmas that Z3 cannot prove by one-step induction, such as the parked `next_permutation`, have a way forward that does not need more fuel or new solver strategies.
- With ADR 0062's exact bounds, Pia gains closed forms and asymptotic claims proved in Lean, so the C++ library's complexity clauses become proved.
- The trusted base gains one component, piac's translation of spec statements into Lean, which is listed in `--trust-report`. It is small and tested in both directions, but a mistake in it can make a Lean proof prove the wrong statement.
- The build gains Lean and Mathlib, several gigabytes, but only in the targets that check Lean proofs, so the edit loop and the default test suite are unchanged.
- Lean proofs are written, not found. Agents can write them, with Lean-auto, Lean-SMT and `grind` doing most of the work, but every Lean-proved lemma is something a person or an agent has to maintain across Lean and Mathlib upgrades.
- New syntax: `by lean Name` as a lemma's or model's body, and the spec form `f in O(g)`. `lean` is a keyword only after `by`.

### Implementation order

Each step is a PR with tests.

1. **Toolchain and a receipt.** Lean as a Bazel module (pinned toolchain, no Mathlib), `piac --emit-lean` for spec functions over `int`, `bool` and records, `by lean` on lemmas, `pia_lean_proof` and receipts, and the round-trip tests. Measure the download size, the cold and warm build times and the disk used.
2. **Certificates and trust report.** The `lean` status in certificates, axioms from `#print axioms`, `--trust-report` and `--why`, `pia-cert audit` replay.
3. **The rest of the translation.** Machine integers as `BitVec`, slices and spec buffers, sums and `let rec` sums, `real` with Mathlib, `--emit-lean --goal`.
4. **Lean models of theories**, and the spectral norm as the first trusted axiom made proved.
5. **Closed forms and `O(...)`**, with Akra–Bazzi, starting with merge sort and heap sort's bounds. This needs ADR 0062's `costs` clauses.

Cost in contracts ([ADR 0062](0062-cost-bounds-in-contracts.md)) needs no Lean and goes first. Step 1 includes a `pia-lean` skill: how to read the generated statements, and which tactics to try first.

**Step 1 as built (2026-11-27).** Four choices differ from or add to the text above:

- The flag is `piac --emit=lean`, like the other emit modes, and receipts come in with `--lean-receipt=<file>`.
- A receipt has one hash, the SHA-256 of the Lean text of the statement and of every definition it uses. It covers the Pia statement too, since the translation is a function of it. The separate Pia statement hash comes with certificates in step 2.
- A spec function with a `requires` is, outside it, an opaque Lean constant `f'outside` applied to the arguments. Pia says nothing about the function there, and Lean can prove nothing about an opaque constant, so no Lean fact depends on how the translation made the function total.
- Lean is an `http_archive` of the release for each host, v4.36.0, about 600 MB compressed per platform, and runs only in `pia_lean_proof` actions, locally rather than on the remote executors. The cold and warm build times are in the PR that built it.

**Step 2 as built (2026-11-27).** Certificates and the trust report:

- The certificate has a `proved lean <lemma> <hash> <theorem> <toolchain> <axioms>` line per proved lemma, in format 3 with the spelling [ADR 0073](0073-prover-identity-abi-version-and-advisories.md) gives per-item Lean lines, so that format holds both ADRs' lines. There is no Mathlib field until Mathlib is in the build.
- One hash, still: the Lean closure hash covers the Pia statement and everything it uses, since the translation is a function of them, so a second Pia hash would add nothing a reader could check that this one does not.
- `native_decide` fails the goal, `[native_decide]`, outside a `@trusted` file. Its axioms are `Lean.ofReduceBool` and `Lean.trustCompiler` in older Lean, and in 4.36 one per use, `T._native.native_decide.ax_1_1`. Inside a `@trusted` file it is a `trusted native_decide` item in the certificate and the trust report.
- `--trust-report` lists each proved Lean lemma after the trusted items, with its theorem, toolchain, axioms and hash, and with `--why` the goals that use it, then how many proved goals use one.
- The translation now types every literal as `Int`. A term of literals alone was a `Nat`, where `0 - 1 = 0` holds, so Lean could prove a statement that is false in Pia.
- `pia-cert audit` replay waits for `pia-cert audit` itself ([docs/abi.md](../abi.md), step 8). Meanwhile a receipt comes only from a `pia_lean_proof` run, and its hash ties it to the statement.

## Answers to the open questions

Dean answered when he accepted it (2026-11-24):

1. **Cost goes first, in its own ADR.** Cost bounds proved by Z3 are [ADR 0062](0062-cost-bounds-in-contracts.md), and they are built before Lean, since they need none of it.
2. **Lean facts need no opt-in.** They are proved, so importers write no `trusting`. `--trust-report` lists them in their own section, with what they rest on (Lean's kernel, Mathlib and piac's translation), and `--why` names the goals that used each.
3. **Mathlib is in scope from the start.** It is already on the iMac. Step 1 still keeps a target without Mathlib for proofs that need only Lean's core, so they stay fast, and it measures the disk Mathlib takes.
4. **Lean is installed on the iMac** for step 1, and the Linux CI job fetches the same pinned toolchain.
