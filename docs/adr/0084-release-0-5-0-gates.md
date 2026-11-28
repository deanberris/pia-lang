# 84. Release 0.5.0: a SAT and SMT solver written in Pia, beside Z3, and its gates

Date: 2026-11-28

Status: Proposed

## Context

The [roadmap](../roadmap.md) (Dean, 2026-11-27, agreed 2026-11-28) makes 0.5.0 the release where the prover Pia trusts can itself be written in Pia, proved, and fast enough to run beside Z3 on the goals `piac` emits. It follows the C++ FFI, which lets a self-hosted front end call Z3 and MLIR first, so the solver is not on the self-hosting critical path.

Dean's decisions that shape it (2026-11-27):

- **Side by side with Z3.** Each certificate names the engines that proved it ([ADR 0073](0073-prover-identity-abi-version-and-advisories.md)); switching away from Z3 is a post-1.0 step.
- **The first SMT theories are chosen by a survey** of the goals the 0.1.0 to 0.4.0 code, the standard library and the demos send to Z3, by theory, count and cost.

## Decision

The release policy of [ADR 0080](0080-release-0-1-0-gates.md) applies.

### Libraries, which gate the 0.5.0 tag

1. **The theory survey**, published: every goal the proof benchmark and the demos send to Z3, grouped by theory (bit-vectors, linear and nonlinear integers, int-blasting, reals and floats, arrays, quantifiers, uninterpreted functions), with counts and costs from `--verify-stats`. It picks the theories the first SMT layer covers.
2. **A CDCL SAT solver in Pia**, in the spirit of CreuSAT: watched literals, clause learning, restarts and an `unsat` proof format such as DRAT, each proved against a model of propositional logic. A reported model satisfies the formula.
3. **A small proof checker**, proved, so a solver's answer is trusted only through its certificate.
4. **Parallel search**: portfolio search on threads, propagation with SIMD or the GPU, using 0.1.0's concurrency and GPU paths and the atomics of [ADR 0052](0052-atomics.md).
5. **The SMT layer** for the theories the survey picks, reading the `smt` dialect goals `piac` emits, with int-blasting as [ADR 0066](0066-int-blasting-for-nonlinear-goals.md) does today.
6. **`piac --solver=pia` and `--solver=both`**: the Pia solver alone, or beside Z3 with any disagreement reported as a bug. Certificates name the engine.

### The demo, which closes the 0.5.x series

- The SAT solver competes on a published set of SAT competition benchmarks, with every `unsat` answer checked by the proved checker.
- The proof benchmark's files are solved by the Pia solver and by Z3, compared on time and goals proved, and published. The Pia solver proves the goals of the theories it covers with no disagreement against Z3.
- The write-up on pia-lang.dev shows the survey, the benchmark and what still needs Z3.

## Consequences

- Z3 stays in the build and the trusted base through 1.0; the Pia solver adds a second engine, not a replacement.
- Goals outside the first layer's theories still go to Z3, and the report says how many.
- The survey becomes a recurring report, re-run each release, to choose the next theory.
