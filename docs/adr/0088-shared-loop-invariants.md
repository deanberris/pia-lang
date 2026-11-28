# 88. Loop invariants every iteration of a spread shares at a collective

Date: 2026-11-28

Status: Proposed

## Context

[ADR 0086](0086-spread-collectives.md) proves a spread with collectives one iteration at a time. At each collective the verifier forgets the cells other iterations own, so an iteration knows its own cells and nothing about anyone else's. That is what makes the proof race free without encoding two iterations, and it is enough for bounds, overflow and ownership.

It is not enough to prove what a spread computes when one iteration's result depends on another's. [pull_spread.pia.md](../pull_spread.pia.md) runs the sediment step as one spread that loops over the waves of the height order. After `exchange flux`, a cell reads its upstream neighbours' loads. To prove that it computes the same step as the sequential one, it has to know that those cells already hold their final loads. Each neighbour's iteration knows that about its own cell, but the cell reading it does not.

GPU verifiers meet the same problem at barriers. GPUVerify's answer is a *barrier invariant*: an assertion each thread proves at the barrier and every thread may then assume for all threads. Pia already has the place to state such a fact. In a spread, a loop that holds a collective runs in step in every iteration, because the protocol check makes its range uniform. So its loop variable means the same thing in every iteration, and so does an invariant written in terms of it.

## Decision

1. **An invariant of a loop that holds a collective is shared.** In a spread, it is an ordinary loop invariant for each iteration. It must also hold at every collective in the loop's body, and there every iteration learns every iteration's instance:

   ```ocaml
   spread q in 0 .. n @owns(flux, pos) do
     for t in 0 .. waves
       invariant wave.[q] < t ==> flux.[order.[q]] = sflux (order.[q])
     do
       exchange flux;
       (* here: forall (q' in 0 .. n). wave.[q'] < t ==> flux.[order.[q']] = sflux (order.[q']) *)
       ...
     done
   done
   ```

   No new keyword is needed: `invariant` already says what holds at each step, and the collective is where the steps of different iterations meet.

2. **Each iteration proves its own instance whatever the others write.** At the collective, the verifier forgets the other iterations' cells, as ADR 0086 does. It then proves the invariant for this iteration (goal: "the loop invariant holds for this iteration at the collective, whatever the others write"), and assumes `forall (q' in lo .. hi). I[q := q']`. An invariant that reads another iteration's cell cannot be proved there, so what each iteration proves is about its own cells, the inputs and uniform values. Every iteration has reached the collective, and no iteration writes another's cells, so in the state at the collective each instance holds, and so does their conjunction.

   An assumed instance about another iteration's cell can go stale once the next phase starts. But an iteration can only read that cell after a later collective, which forgets it again, or in a buffer a collective published, which no iteration writes until the next collective. So a stale fact is never used.

3. **The invariant may name only shared things.** It may name the spread's variable, the variables of the loops around the collective that hold collectives, names bound before the spread, and spec functions. Naming a value this iteration computed, such as `let c = order.[q]`, is a compile error: in another iteration's instance it would mean another value. The error names it and says what may be named.

4. **The loop's own entry and exit are not collectives.** The barriers ADR 0086 places before and after a loop that holds a collective belong to the code around the loop, so the loop's invariants are not shared there. The invariant still holds at the loop's exit for each iteration, as any loop invariant does.

## Consequences

- `pull_spread.pia.md` proves that one spread leaves every cell's load, bed and inflow equal to a function of the input, and from that the same bed and loads as the sequential step, through pull.pia.md's `same_step`.
- A spread whose loops have invariants that do not hold at their collectives no longer proves. Collectives landed the same day (#567), and no program has such a loop, so this needs no migration rule.
- A gathered argument is still known only at the iteration's own cell. So a collective's result, such as a `sum`, is known only through its contract at that cell. Making a whole gathered array known when its argument reads only published and read-only data is a possible next step. Until then, `pull_spread.pia.md` adds up its outflow after the spread.
