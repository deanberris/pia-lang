# 53. Protocols and deadlock are checked in Z3, as transition systems proved by constrained Horn clauses; explicit search stays for atomics, and TLA+ is an export format

Date: 2026-11-23

Status: Accepted (2026-11-27)

## Context

[ADR 0027](0027-coroutines-and-race-freedom.md) plans a model checker for what the type system cannot express: the library's primitives, channel protocols, deadlock, and user code built from atomics ([docs/concurrency.md](../concurrency.md#4-the-model-checker), sections 4 and 5). It is to be an exhaustive explicit-state search with dynamic partial-order reduction (DPOR), as in Nidhugg, GenMC and Loom, where a search that hits its limit is unproved. [ADR 0050](0050-senders-and-receivers.md) adds a goal for it, the in-flight slot table's stop race, and [ADR 0052](0052-atomics.md) adds RC11 with a battery of litmus tests. Nothing of the checker is built.

Dean asked (2026-11-23) whether the checker could use TLA+ as a library, or whether this could just be a theory that Z3 handles.

- **TLA+ as a library.** TLC, the explicit-state checker, and Apalache, the symbolic one, both run on the JVM, and neither is a library to link. Using them would put a Java runtime and a second specification language inside `piac`'s proof path. Their results would also be outside what the certificate ([ADR 0024](0024-published-proof-certificates.md)) and `--trust-report` record about a goal.
- **Z3 already decides most of it.** A protocol is a transition system: states, an initial condition, and a transition relation. Deadlock freedom, exactly-once delivery and mutual exclusion are safety properties, each saying that no reachable state is bad. Z3's Spacer engine proves safety of transition systems without a bound, by solving constrained Horn clauses (CHC). It finds an inductive invariant, or a counterexample trace if one exists, which is what IC3 and PDR do for hardware. That is the approach Apalache takes for TLA+, except here it runs in the process.
- **The front end exists.** The prelude's `machine` metaprogram ([docs/theories.md](../theories.md#state-machines), [ADR 0036](0036-library-theories.md)) already turns a table of transitions into a theory with a model. ADR 0027's protocol inference produces automata of the same kind for each channel end.

## Decision

### 1. Safety goals are CHC queries discharged by Spacer

A protocol goal becomes a transition system, and its safety property becomes three kinds of Horn clauses over an invariant predicate `Inv`. The initial states satisfy `Inv`. A transition from an `Inv` state reaches an `Inv` state. No `Inv` state is bad. Z3 solves the clauses with Spacer:

- **Proved** when Spacer returns an invariant. The invariant is kept as the goal's witness, so the proof cache ([ADR 0032](0032-parallel-sliced-cached-proving.md)) and the certificate store it, and checking it again later is three ordinary SMT queries, not a new search.
- **Failed** when Spacer returns a derivation. That is a trace of transitions from an initial state to a bad one. `piac` prints it as a schedule with source locations, as ADR 0027 already plans for counterexamples, and `Pia.Task.run_deterministic` replays it.
- **Unproved** when Spacer runs out of budget, which is a compile error like any unproved goal, accepted only by `--allow-unproved`. Bounded unrolling (BMC) is used only to find a counterexample sooner. A bounded "no counterexample" is never a proof, as ADR 0027 requires.

The verifier reaches Z3 directly through its C++ API already (`src/verify/Strategy.cpp`), so the CHC queries go through `z3::fixedpoint`, or through `HORN` logic, beside the `smt` dialect's per-goal queries rather than through it.

### 2. What becomes a transition system

- **Channel protocols and deadlock** (ADR 0027, section 5, stages 2 and 3). The state is each task's protocol automaton state together with each channel's occupancy, and data is abstracted to what the protocols read. The bad states are those where a set of tasks is blocked forever on one another. The topology check and the pattern lemmas still come first. Spacer takes what they leave, in place of the explicit search.
- **Parametric claims.** A worker pool of `n` tasks is a transition system over a counter of tasks in each state, which is a counter abstraction. Spacer then proves it for every `n` at once, where an explicit search needs a cutoff lemma.
- **Library protocols.** These include the in-flight slot table and stop tokens (ADR 0050, section 4), `once`, the barrier, and the channel's own implementation above its atomics. Each is a `machine`, or an inferred automaton, with its invariant proved once when the library builds.
- **Generated state machines in user code**, such as a connection's states. These stay theories as today, and Spacer adds the reachability questions a `machine` theory alone cannot answer: "can `Draining` be reached without `shutdown`?"

### 3. Explicit DPOR stays for fine-grained atomics

Code over atomics under RC11 (ADR 0052) has interleavings at every load and store, and a symbolic encoding of that grows with every pair of events. DPOR over the event graph, as GenMC does, is the known good approach. So the explicit checker remains, with a narrower job: the primitives built directly on atomics (the work-stealing deque, the mutex's fast path, the channel's ring) and user code that uses atomics. Its litmus battery is ADR 0052's. Everything above the atomic layer, where a protocol's steps are whole operations, goes to Spacer.

### 4. Liveness is reduced to safety

"Every operation eventually completes" and "a waiting task is eventually woken" are liveness properties, which need fairness. Two reductions cover the cases Pia needs:

- **Ranking functions.** A protocol whose progress has a measure, such as the operations left in the slot table or the items left in a bounded channel, proves liveness as a safety property: the measure decreases on every fair step. That is how `decreases` already works for loops.
- **Liveness to safety.** For the rest, the standard construction of Biere, Artho and Schuppan turns "no fair infinite run avoids the goal" into a reachability query over a doubled state, which Spacer then decides.

A liveness goal that neither discharges is unproved. ADR 0027's channel deadlock goal is a safety property, so it needs neither.

### 5. TLA+ is an export, not a dependency

`piac --emit=tla` writes a goal's transition system as a TLA+ module: its variables, `Init`, `Next`, the invariant to check and, when proved, Spacer's invariant as a candidate inductive invariant. It lets someone cross-check a protocol with TLC or Apalache, or read it as a specification. Nothing in the build depends on it, and its results are not proofs to `piac`.

## Implementation steps

1. **CHC goals in the verifier**: a goal kind for transition systems, queried through `z3::fixedpoint` with Spacer. Invariants are stored in the proof cache and re-checked as three SMT queries. Traces are printed as schedules.
2. **`machine` reachability**: theories built by `machine` get reachability and invariant goals. This is the first user-visible use, and it needs no tasks.
3. **ADR 0050's slot table and stop tokens**, as the first library protocol proved this way.
4. **Channel deadlock, stages 2 and 3** (#112, #113), on protocol automata, with counter abstraction for parametric topologies.
5. **Liveness** by ranking functions, then by liveness to safety.
6. **`--emit=tla`**.
7. **Explicit DPOR for atomics** (#81, #83), against ADR 0052's battery.

## Consequences

- Most of the model checker becomes a goal kind in the existing verifier, using the solver and proof cache Pia already has, instead of a separate search engine. Its proofs are invariants that can be re-checked cheaply and recorded in certificates.
- Parametric protocols, such as a pool of `n` workers, are proved for every `n` without hand-written cutoff lemmas.
- Spacer can fail to converge on some protocols, and those goals are unproved. The explicit checker is still needed for atomics, so Pia keeps two engines, each with a narrower job than ADR 0027 planned for one.
- TLA+ users can read and check Pia's protocols with their own tools, and Pia does not depend on them.

## Questions for Dean

1. **Should the explicit DPOR checker be built at all?** The recommendation is yes, but last, and only for code directly over atomics. The alternative is to encode RC11 executions as CHC too, which avoids a second engine at the cost of queries that may not scale. Answered 2026-11-27 by Dean: yes, built last, only for code directly over atomics.
2. **What is Spacer's budget per goal?** The recommendation is the verifier's usual per-goal rlimit ([ADR 0032](0032-parallel-sliced-cached-proving.md)), scaled by a per-goal `@solver` setting for large protocols. The alternative is a separate, larger default for CHC goals. Answered 2026-11-27 by Dean: the usual per-goal rlimit, scaled by `@solver`.

## Prior art

| Source | What Pia takes |
| --- | --- |
| Z3's Spacer (Komuravelli, Gurfinkel and Chaki), IC3 and PDR (Bradley, Een) | safety of transition systems by CHC, with inductive invariants as certificates |
| Apalache | symbolic checking of TLA+ in an SMT solver |
| TLA+ and TLC | the specification format that `--emit=tla` writes |
| Counter abstraction (Pnueli, Xu and Zuck) | parametric protocols as counts of tasks in each state |
| Biere, Artho and Schuppan, liveness to safety | liveness goals as reachability queries |
| GenMC, Nidhugg, Loom | explicit DPOR for code over atomics |
