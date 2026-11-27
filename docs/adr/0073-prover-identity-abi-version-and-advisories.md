# 73. Certificates record who proved a module and with what, advisories revoke trust in faulty provers, and every breaking change ships a migration

Date: 2026-11-26

Status: Accepted (2026-11-26, from Dean's answers on the design questions)

## Context

A Pia certificate ([ADR 0024](0024-published-proof-certificates.md), `src/cert/Certificate.h`) says which interfaces an object provides, which it was proved against, and (format 2) its own trusted items. It does not say which compiler proved it. A certificate stands for "piac proved every goal", so it is only as sound as the piac, Z3 and Lean that did the proving. If we find a soundness bug in piac (a goal never emitted, an encoding that drops a hypothesis, an interval rule that proves too much) or in a solver, every object that bug may have touched carries a certificate that is no longer worth what it says, and today nothing can tell those objects apart from good ones.

[docs/abi.md](../abi.md) already plans for parts of this. Its certificate header has a Pia ABI version and a target, its image record has a "compiler identity", the Layer 2 check may require "the compiler identity is in an allowed set", and "Proof and build identity" lists the compiler version, a hash of the `piac` binary and the Z3 version. None of it is built: format 2 has no header fields beyond magic, format and length, and `piac` has no version (`MODULE.bazel` says `0.0.0`, and there is no `piac --version`). [ADR 0061](0061-lean-proved-facts.md) gives every Lean-proved item a receipt naming the Lean toolchain, the Mathlib commit and the axioms, which the certificate should carry too.

Dean asked (2026-11-26) for four things: encode the compiler version that proved a module and its interfaces, encode ABI compatibility, have a way to mark modules whose proofs may be faulty because of a bug in an earlier compiler so that they are not trusted, and an automated way to migrate code from one Pia version to the next: every new or deprecated feature comes with transformation rules, so the compiler either rewrites old code mechanically or rejects it with a suggestion a person or an agent can follow.

The last ask is the other half of the first three. A revoked module is fixed by rebuilding it with a newer piac, and that only works if the newer piac still accepts the module's source, or says exactly how to change it. Pia changes every week until 0.1.0 (ADRs 0064, 0069, 0071 and #453 all change what valid source looks like), and today a change in syntax or meaning just breaks old code with whatever error the new parser happens to give.

Prior art:

- **Rust** records the compiler version in every `.rlib` and refuses to link crates built by another `rustc`. That is ABI compatibility, not soundness: it has no way to say "1.52.0 had a miscompile, distrust what it built" (the 1.52.1 incremental-compilation bug was handled by a point release and an advisory blog post).
- **RustSec, Go's vulnerability database and OSV** publish advisories as data: an id, the affected package, version ranges introduced and fixed, and optionally the affected symbols, so `govulncheck` reports only programs that reach the faulty function. Tools ship a copy and can be given a newer one.
- **Certificate revocation (CRLs, Apple's notarization revocation)** marks a signed thing untrusted after the fact without changing the thing.
- **Proof assistants** (Lean, Coq) record the kernel and library versions in `.olean`/`.vo` files and refuse mismatched ones, and Lean's `#print axioms` lists what a proof rests on. Narrowing distrust to "proofs that used feature X" is what an axiom list makes possible.

- **Migrations.** Rust editions with `cargo fix --edition` (each lint that guards an edition change carries a machine-applicable suggestion), Go's `go fix` and `gofmt -r`, clang-tidy and Clang fix-its, Swift's migrator, Python's `2to3` and OpenRewrite's recipes all rewrite old source to new. The ones that work best attach the rewrite to the diagnostic that reports the old form, so the same rule serves the compiler, the editor and the batch tool, and they mark which suggestions are safe to apply blindly and which need a human.

The Pia-specific point is that a soundness bug rarely touches every proof. Most bugs live in one rule: a lint's rewrite, int-blasting, the Presburger path, interval analysis, the float rounding model, a lemma cache. If the certificate records which proof engines a module's goals actually used, an advisory can name an engine and a version range, and only the modules that used that engine in that range lose trust.

## Decision

### 1. The certificate records the prover

Certificate format 3 adds lines to the text body, after `module`:

```text
module Image.Pixels
abi 1 arm64-apple-macos
prover piac 0.1.0+512.9f3c2e1a7b04
solver z3 4.15.4
engines intervals,z3,int-blast,presburger
lean leanprover/lean4:v4.25.0 mathlib 3c1b2d0e 2
provides Image.Pixels.Ops <hash>
requires Image.Pixels.Ops <hash>
trusted lowering matmul <hash> linalg.matmul
```

- `prover` is piac's identity: the release version and, for builds between releases, the number of commits on `main` since the root and the short commit (`0.1.0+512.9f3c2e1a7b04`). The commit count makes builds on `main` totally ordered, so an advisory can name a range. Bazel stamping (`--config=release`, `src/version/workspace_status.sh`) puts it into the piac that CI publishes. Every other build, including CI's own build and test run, records `piac dev`, which no advisory range covers and which a deployment policy can refuse (`pia-cert check --require-released`).
- `solver` names each SMT solver that decided a goal, with its version. Today that is only Z3. The options that change what a proof means (none do today; strategies and rlimits only change whether a proof is found) would be listed here if any ever did.
- `engines` is the set of proof engines that discharged at least one of the module's goals, from a fixed list in the verifier: `intervals` (interval analysis), `z3` (default solver), `int-blast` ([ADR 0066](0066-int-blasting-for-nonlinear-goals.md)), `presburger` ([ADR 0020](0020-presburger-for-affine-goals.md)), `nlsat` and `float-model` ([ADR 0038](0038-float-kernels-against-real-theories.md)), `uf-div` (division as uninterpreted functions, [verifier.md](../verifier.md)), `theory:<name>` per library theory ([ADR 0036](0036-library-theories.md)), `lemma-cache` (certified instances skipped by importers, [ADR 0043](0043-generic-definitions-proved-once.md)), `generic` (an instance proved by its generic's proof over sorts, ADR 0043), `proof-cache` (a goal answered by `--proof-cache`), `lean` and `refinement` (ABI baselines). An engine is added to the list in the same PR that adds the engine. The verifier already knows which path proved each goal (`--verify-stats` counts them), so this is a set union, not new analysis.
- `lean` appears once per Lean toolchain and Mathlib commit used, with the number of receipts. Each Lean-proved item is also a line `proved lean <item> <receipt hash>`, so an advisory against one Lean proof can be precise.
- `abi` is the **Pia ABI version** ([docs/abi.md](../abi.md#abi-evolution)), a single integer in `src/cert/Certificate.h`, and the target triple. It starts at 1. It covers the calling convention, the canonical `.piai` serialisation the interface hashes are taken over, and the certificate format's meaning. The link check refuses two objects with different ABI versions or targets, with the message "built by a piac with Pia ABI 1; this one has ABI 2: rebuild it". The ABI version is also the first thing hashed into every interface hash, as ADR 0024 already says, so a bump changes every witness symbol and dyld refuses a mismatch without the runtime check.

The prover is not hashed into the interface hash or into any witness. Upgrading piac must not, by itself, break every importer: a new compiler with the same ABI version proves the same interface to the same hash. The prover is policy and audit data, which is what ADR 0024 and abi.md already say for "compiler identity".

piac keeps writing the lowest format that holds what it writes (format 1 without trusted items, format 2 with them), until format 3 is written by every piac: from then on every object has an `abi` and a `prover` line, so a format 1 or 2 certificate is itself evidence of a build from before this ADR, and `pia-cert check` treats it as `piac unknown` (see 3).

`piac --version` prints the same identity, the solver versions and the ABI version.

### 2. Advisories say which proofs are faulty

An **advisory** is a small file, `PIA-2026-0001.toml`, in `security/advisories/` in this repository:

```toml
id = "PIA-2026-0001"
summary = "Interval analysis proved u32 subtraction cannot wrap when the bounds came from a loop invariant"
piac = { introduced = "0.0.0+380", fixed = "0.1.0+514" }
engines = ["intervals"]          # optional: only modules whose certificates name one of these
solver = {}                      # or { z3 = { introduced = "4.15.0", fixed = "4.15.2" } }
lean = []                        # or receipt hashes of individual Lean proofs
severity = "unsound"             # unsound: a proved goal may be false; incomplete: never revokes
fixed_by = "https://github.com/deanberris/pia-lang/pull/530"
```

A certificate **matches** an advisory when its `prover` is in the advisory's piac range (or its `solver` in the solver range, or one of its Lean receipts is listed), and, if the advisory names engines, the certificate's `engines` contains one of them. An advisory with no engines matches every certificate in its range: that is the right answer when we do not know which rule was at fault.

Advisories are data, not code, and are reviewed like any PR. Publishing one is the response to a soundness bug, together with the fix and a regression test in `tests/verify/` that the faulty piac proved and the fixed one refuses. The advisories are also published on the documentation site.

### 3. Checks refuse matching modules

- **`pia-cert check`** (and so every `pia_library` and `pia_binary` validation action, and `piac link`) reads the advisories and refuses an object whose certificate matches one, naming the advisory, the module, the engine and the fix: "Image.Pixels was proved by piac 0.0.0+402, which PIA-2026-0001 says may prove false goals with interval analysis, and its proofs used interval analysis: rebuild it with piac 0.1.0+514 or later". It also refuses a missing or older-format certificate's `piac unknown` once format 3 is the only format piac writes, unless the deployment allows it.
- **Importers.** A module proved against an interface whose provider is revoked is not itself unsound (its proof is assume-guarantee), but the program is. The check reports every revoked object, and, transitively, which programs and libraries contain or load one.
- **Accepting a revocation.** `pia-cert check --accept-advisory=PIA-2026-0001:Image.Pixels` lets that one module through. An accepted advisory becomes a trusted item of the image, listed by `--trust-report` like an `@assume`, so trusting a known-faulty proof is visible and never silent. This follows [ADR 0004](0004-strongest-guarantee-by-default.md): the strongest guarantee is the default, and weakening it is explicit and narrow.
- **Rebuilding.** Proofs are deterministic under an rlimit ([ADR 0032](0032-parallel-sliced-cached-proving.md)), so the fix for a revoked module is to rebuild it with a fixed piac. In Bazel that happens anyway when piac changes. `pia-cert check --why` lists the modules to rebuild, and an advisory against a library someone else ships says which version to ask for.
- **The proof cache.** A proof cache entry is keyed by the Z3 version, the rlimit and the query, not by piac, and a piac bug produces a wrong query, not a wrong answer about a query: the cached fact "this query is unsat" is still true. So piac advisories never purge the cache. A solver advisory does: piac refuses cache entries made by a revoked solver version, which the key already contains.
- **Launch and `Pia.Dl.open`.** The runtime's certificate check (abi.md, Layer 2, not built yet) will check the ABI version and the advisories compiled into the runtime that was linked. A loader cannot fetch newer advisories, so this catches only what was known when the program was built. `pia-cert audit` on a built program, with the current advisories, is how a deployment finds out later.

### 4. Where advisories come from

The advisories in `security/advisories/` are compiled into `pia-cert`, `piac` and the runtime at build time, so every tool knows every advisory older than itself. `pia-cert check --advisories=<dir>` adds a newer set, so an old toolchain can be checked against today's list. `pia-cert advisories` lists them.

### 5. Every breaking change ships a migration

A **breaking change** is any change after which some source that piac accepted is rejected or means something else: a renamed keyword, a new syntax, a removed feature, a changed default, a stdlib interface that drops a baseline. A PR that makes one adds a **migration rule** for it, in the same PR, in `src/migrate/rules/`. A rule has:

- an id and the piac version that introduces it (the `prover` identity of section 1, so `0.1.0+530`);
- a **matcher** over the parsed (not yet expanded) syntax tree, which finds the old form;
- either a **rewrite** to the new form, or a **suggestion**: a message saying what to change and why, with the new form spelled out where it can be, for when no mechanical rewrite is safe (a meaning that depends on intent, such as which of two new keywords an old one should become);
- a test: `before.pia`, `after.pia` (or the expected suggestion), proved by the test runner like every `tests/verify` file.

Rules run in two places.

- **In piac, every build.** For one release after the change, piac still parses the old form and reports it as a `deprecated` warning with the rewrite attached as a fix-it. After that, the old form is an error, but the rule keeps running on the error path, so the error says what to write instead, forever. A rule never silently accepts old source: a warning or an error always names the rule. The language server shows the same fix-it as a code action, and the REPL and `pia mcp` return it in the cell's diagnostics, so an agent sees the exact edit.
- **In `piac migrate`.** `piac migrate [--from=<version>] [--check] <files>` applies, in version order, every rule introduced after `--from` (default: the oldest), rewriting files in place, then proves the result. Rewrites must be idempotent and must leave the file's comments and layout as they were outside the rewritten span. Suggestions that have no rewrite are printed as a list of `file:line: [rule] what to do`, the same shape as lints, so a person or an agent works through them. `--check` changes nothing and fails when any rule would fire, which is how CI keeps `lib/`, `tests/`, `examples/` and the docs migrated.

**A rewrite is checked by proof, not trusted.** After `piac migrate`, the new source must prove, and where the old and new forms both elaborate (during the deprecation release) the rule's test also checks that both produce the same `pia_contract` obligations and the same interface hash. A rewrite that changes an interface hash is a breaking change to the module's ABI as well, and `piac migrate` says so.

**Enforced in CI.** `tools/migrate/check.py` fails a PR that changes the grammar (`src/syntax`), a keyword table, a lint's default level or a stdlib interface baseline without adding or updating a rule, unless the PR's description says `no-migration: <why>` (for example, a change that only accepts more programs). Like `tools/skills/check.py`, it makes the missing piece impossible to forget, not impossible to skip with a reason.

**Skills.** The `pia-porting` and `pia-language` skills point agents at `piac migrate` and the fix-its, and a new or deprecated feature's skill change (CLAUDE.md's skill-pack rule) names its migration rule.

**Connection to advisories.** An advisory's fix is "rebuild with a fixed piac". When that piac is newer than the source, `pia-cert check --why` says to run `piac migrate --from=<the old prover's version>` first, which it knows from the certificate's `prover` line. That is why certificates record the version even for modules nothing revokes.

## Consequences

- Every Pia object says who proved it, with what solvers and engines, and for which ABI, and `pia-cert dump` shows it.
- A soundness bug becomes an advisory, a fix and a regression test. Builds that contain a module the bug may have touched stop at the next check, and only those: a bug in interval analysis does not revoke modules that never used it.
- Trusting a revoked proof is possible, but it is a listed trusted item, never a default.
- Upgrading piac does not break importers. Bumping the ABI version breaks all of them, by design, and is rare.
- Only the published piac is stamped. A stamped piac changes with every commit, so stamping every build would rerun every test that runs piac on every pull request, even one that changes only docs or `lib/`. CI builds and tests with `piac dev`, then relinks piac once with `--config=release` to publish it, and checks the stamp on pull requests by building only the stamped header.
- The `engines` line depends on which engine proved each goal, which is reproducible under an rlimit. If a later change makes engine choice depend on timing, the certificate would not be reproducible, so engines must stay deterministic.
- Advisories rest on the trust model ADR 0024 already states: they make honest-but-buggy builds safe to combine, and they do nothing against a malicious producer, who can write any `prover` line. Code signing and, later, re-checkable proof objects are the answer there.
- Every breaking change costs a rule and a test in the same PR, and in exchange old code is never stranded: it migrates in one command, or fails with the exact edit to make. Deprecated forms cost one release of parser support each.
- Because rules key on piac versions, the version identity of section 1 is a dependency of migration, not only of trust.
- An advisory can only be as narrow as the engine list. A bug in goal generation (a goal never emitted) is not in any engine, so its advisory names no engines and revokes every module in the range. A later refinement could record which goal kinds a module raised, if advisories turn out to be too broad.

## Implementation

1. **Identity.** `piac --version`, Bazel stamping in CI and release builds, and the `prover`, `solver` and `abi` lines in a format 3 certificate. The link check refuses mismatched ABI versions and targets. `pia-cert dump` prints the new lines. Skills: `piac-build` (the new lines, `--version`).
2. **Engines and Lean.** The verifier records which engine proved each goal and writes the `engines` line and the Lean receipt lines.
3. **Advisories.** The TOML format, `security/advisories/`, compiled into `pia-cert`; `pia-cert check` refuses matches, `--accept-advisory`, `--advisories=<dir>`, `--require-released`, `pia-cert advisories`; accepted advisories in `--trust-report`. A test advisory against a fake engine, with objects that match and do not. Skills: `piac-build` and `piac-verify` (the flags), and a page on the site.
4. **Proof cache.** Refuse cache entries from a solver version an advisory revokes.
5. **Migration framework.** `src/migrate`, rules over the syntax tree with rewrites and suggestions, `deprecated` warnings with fix-its in piac, the LSP code action and REPL/MCP diagnostics, `piac migrate` with `--from` and `--check`, and a first rule for the next breaking change that lands. Skills: `piac-build` (the command), `pia-idioms` (the `deprecated` warning).
6. **The CI rule.** `tools/migrate/check.py` in CI, and `piac migrate --check` over the repository.
7. **Runtime.** The launch check, when the runtime's certificate check from abi.md Layer 2 lands.

## Decisions on the design questions

Dean answered each question on 2026-11-26, in every case with the proposal:

1. **Granularity.** An advisory names a version range, narrowed by the proof engines a module's certificate lists. An advisory with no engines revokes every module in its range.
2. **Response.** The check refuses a module that matches an advisory, unless that module is accepted by name with `--accept-advisory=ID:Module`, which makes it a trusted item.
3. **Build identity.** Builds between releases are the release version plus the commit count on `main` and the short commit (`0.1.0+512.9f3c2e1a7b04`). Unstamped builds are `dev`.
4. **Distribution.** Advisories are checked in under `security/advisories/` and compiled into piac, pia-cert and the runtime. `--advisories=<dir>` adds a newer set. Nothing is fetched over the network.
5. **Deprecation.** A deprecated form keeps compiling for one release with a `deprecated` warning and a fix-it, then becomes an error that still names the fix.
6. **Source version.** Source does not declare a Pia version. Rules detect old forms from the source, and `piac migrate --from` takes a version from the user or from a certificate's `prover` line.
