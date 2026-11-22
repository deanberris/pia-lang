# A catalogue of theories

A *theory* teaches the verifier about a domain. It declares new sorts, functions on them that have no body, and axioms about them, and it lives in a library, not in the compiler ([ADR 0036](adr/0036-library-theories.md)). This page is a catalogue of worked theories. Each one shows the theory, a model that proves its axioms, a proof that uses the theory, and a mistake that the theory catches.

!!! note "Status"
    Theories, models and sealing are implemented (ADR 0036, steps 1 to 5), and the documentation test proves every example below with `piac --verify`, and checks that each mistake fails. Consistency checks of trusted theories, `--trust-report --why` and `import ... trusting` (step 4) are implemented too. Theory-building metaprograms (step 5) are implemented too, so every example on this page is proved, and so are solver strategies and tactics (step 6). `piac --verify --check-vacuity` (step 7) checks that no goal proved with a trusted axiom was proved from a contradiction ([verifier.md](verifier.md#theories)).

## How to read an entry

Every theory has the same four parts.

1. **The theory.** A `sig` of sorts (`let sort`), abstract spec functions (`let spec` with no body) and axioms (`let axiom`). Everything in it is spec-only: it can appear in contracts, spec functions and lemmas, and codegen erases it.
2. **The model.** A `struct` that gives each sort a concrete type and each function a definition, so that every axiom becomes a lemma the solver proves. A theory with a proved model cannot contradict itself, so its axioms cannot make the verifier accept a false goal. Then the model is sealed: code that imports the theory sees the axioms, never the model.
3. **A proof that uses it.** A lemma or a function contract that the axioms prove.
4. **A mistake it catches.** A version that is wrong and fails with a counterexample.

A module cannot import another's theory yet, since interfaces do not carry theories, so each entry is one program, with the theory, its model and its clients together. A client still sees only the theory's axioms, because the model is sealed. The report under each program shows the lines that matter: the client's goals, and the model meeting each axiom. When a theory has a model, a counterexample is found in the model, where everything is concrete, and the report says so: a goal that is false in a model that meets the axioms is not a consequence of them.

An entry also says whether anything in it is **trusted**. A trusted theory has no model that the program can find, so it is declared in a `@trusted` module and imported with `trusting`. Trust covers the whole theory, and the compiler lists every axiom it brings in `piac --trust-report`.

| Theory | What it proves | Trusted | Tested from |
| --- | --- | --- | --- |
| [Lock levels](#lock-levels) | a lock discipline rules out lock-order deadlock | nothing | step 3 |
| [Happens-before](#happens-before-and-memory-orders) | release/acquire publishes data, relaxed does not | nothing | step 3 |
| [Probability](#probability) | union bounds on failure; independence as an explicit trust | `independent` only | steps 3 and 4 |
| [Fail-safe control](#fail-safe-control) | a controller falls back to a safe command on a sensor fault | nothing | step 3 |
| [State machines](#state-machines) | a protocol is followed, from a table of transitions | nothing | step 5 |
| [Clocks](#clocks-a-proof-written-by-a-tactic) | elapsed time over many ticks, by induction that a tactic writes | nothing | step 6 |
| [Units of measure](#units-of-measure) | quantities are combined with the right dimensions | nothing | step 3 |
| [Network shapes and bounds](#network-shapes-and-bounds) | layer shapes match and Lipschitz bounds compose | nothing | step 3 |
| [Allocators](#allocators) | a block from `take` aliases no live block, and a given-back block is dead | nothing | step 3 |

The steps are the implementation order of ADR 0036: (1) spec-only `real` and `int`, (2) theories in `@trusted` modules, (3) models and sealing, (4) certificates and `trusting`, (5) theory-building metaprograms, (6) solver strategies and tactics, (7) `--check-vacuity`.

## Lock levels

[ADR 0027](adr/0027-coroutines-and-race-freedom.md) rules out lock-order deadlock with static lock levels: a task may only take a lock above every level it holds. The compiler checks Pia's own `mutex` that way. A library with its own lock discipline, such as a database lock manager or a kernel's spinlock hierarchy, can state the same rule as a theory, and the verifier then checks it in that library's users.

`held` is the set of levels a task holds, and `below h n` says every held level is less than `n`:

<!-- example: levels.pia -->
<!-- expect: fail -->
```ocaml
let level = type int{0..63}

let theory Levels = sig
  let sort held
  let spec none : held
  let spec take : (h : held) -> (n : level) -> held
  let spec drop : (h : held) -> (n : level) -> held
  let spec holds : (h : held) -> (n : level) -> bool
  let spec below : (h : held) -> (n : level) -> bool

  let axiom none_below (n : level) ensures below none n
  let axiom take_holds (h : held) (n : level) (m : level)
    ensures holds (take h n) m = (m = n || holds h m)
  let axiom drop_holds (h : held) (n : level) (m : level)
    ensures holds (drop h n) m = (m <> n && holds h m)
  let axiom take_below (h : held) (n : level) (m : level)
    requires below h n && n < m
    ensures below (take h n) m
  let axiom drop_below (h : held) (n : level) (m : level)
    requires below h m
    ensures below (drop h n) m
  let axiom below_held (h : held) (n : level) (m : level) @trigger(below h n, holds h m)
    requires below h n && holds h m
    ensures m < n
end

\ Levels are bits of a u64: bit n is set when level n is held.
let model bits : Levels = struct
  let sort held = u64
  let spec none : u64 = 0
  let spec take (h : u64) (n : level) : u64 = (h | (1 << n))
  let spec drop (h : u64) (n : level) : u64 = h & ~(1 << n)
  let spec holds (h : u64) (n : level) : bool = ((h >> n) & 1) = 1
  let spec below (h : u64) (n : level) : bool = (h >> n) = 0
end

\ accounts are level 2 and the ledger is level 3
let lemma transfer_order (h : Levels.held) : unit
  requires Levels.below h 2
  ensures Levels.below (Levels.take h 2) 3
= ()

let lemma ledger_then_account (h : Levels.held) : unit
  requires Levels.below h 3
  ensures Levels.below (Levels.take h 3) 2
= ()
```

```console
$ piac --verify levels.pia
...
levels.pia:40:3: proved: the postcondition holds [smt]
levels.pia:45:3: failed: the postcondition holds
  counterexample in the model 'bits': h = 0
...
levels.pia:24:5: proved: the model 'bits' meets the axiom 'Levels.below_held' [smt]
19 proved, 1 failed, 0 skipped
```

The model's obligations are bit-vector facts, such as `(h >> n) = 0 && n < m ==> ((h | (1 << n)) >> m) = 0`, which Z3 decides. `piac` proves each axiom as a lemma over the model, and reports it as `the model 'bits' meets the axiom ...`.

A lock manager's `acquire` takes the task's held set as a ghost argument and requires the new level to be above it, and its users prove their own lock orders from the axioms: `transfer_order` proves. Taking the ledger first and then an account, `ledger_then_account`, is the deadlock the rule exists to prevent, and it fails.

The counterexample is in the model: from `h = 0`, taking level 3 sets bit 3, and `3 >> 2` is not 0, so the held set is not below 2. Over the axioms, `take_holds` says the task now holds level 3, and `below_held` says a held level must be below 2. `below_held` needs a written trigger with two terms, since neither `below h n` nor `holds h m` mentions all three of its parameters.

## Happens-before and memory orders

[ADR 0027](adr/0027-coroutines-and-race-freedom.md) counts a happens-before edge from atomics only when the memory orders create one: a `release` store read by an `acquire` load. The usual bug is publishing data with a flag written `relaxed`. As a theory, the rule is four axioms over events:

<!-- example: order.pia -->
<!-- expect: fail -->
```ocaml
let theory Order = sig
  let sort event
  let spec po : (a : event) -> (b : event) -> bool        \ program order, one thread
  let spec rf : (w : event) -> (r : event) -> bool        \ r reads the value w stored
  let spec releases : (w : event) -> bool                 \ a store at release or stronger
  let spec acquires : (r : event) -> bool                 \ a load at acquire or stronger
  let spec hb : (a : event) -> (b : event) -> bool        \ happens before

  let axiom po_hb (a : event) (b : event) requires po a b ensures hb a b
  let axiom sync_hb (w : event) (r : event)
    requires rf w r && releases w && acquires r
    ensures hb w r
  let axiom hb_trans (a : event) (b : event) (c : event) @trigger(hb a b, hb b c)
    requires hb a b && hb b c
    ensures hb a c
  let axiom hb_irrefl (a : event) ensures hb a a = false
end

\ Every event gets a global time: a sequentially consistent execution.
let stamp = type { thread : u32; time : int; rel : bool; acq : bool; read_from : int }

let model timeline : Order = struct
  let sort event = stamp
  let spec po (a : stamp) (b : stamp) : bool = a.thread = b.thread && a.time < b.time
  let spec rf (w : stamp) (r : stamp) : bool = r.read_from = w.time && w.time < r.time
  let spec releases (w : stamp) : bool = w.rel
  let spec acquires (r : stamp) : bool = r.acq
  let spec hb (a : stamp) (b : stamp) : bool = a.time < b.time
end

let lemma publish (data_w : Order.event) (flag_w : Order.event)
                  (flag_r : Order.event) (data_r : Order.event) : unit
  requires Order.po data_w flag_w && Order.releases flag_w
  requires Order.rf flag_w flag_r && Order.acquires flag_r
  requires Order.po flag_r data_r
  ensures Order.hb data_w data_r
= ()

let lemma publish_relaxed (data_w : Order.event) (flag_w : Order.event)
                          (flag_r : Order.event) (data_r : Order.event) : unit
  requires Order.po data_w flag_w
  requires Order.rf flag_w flag_r && Order.acquires flag_r
  requires Order.po flag_r data_r
  ensures Order.hb data_w data_r
= ()
```

```console
$ piac --verify order.pia
...
order.pia:36:3: proved: the postcondition holds [smt]
order.pia:44:3: failed: the postcondition holds
  counterexample: data_w = Order.event!val!0, flag_w = Order.event!val!1, flag_r = Order.event!val!2, data_r = Order.event!val!3
...
order.pia:16:35: proved: the model 'timeline' meets the axiom 'Order.hb_irrefl' [smt]
5 proved, 1 failed, 0 skipped
```

The message-passing idiom, `publish`, proves: the data store is before the flag's release store in its thread, the flag's acquire load reads it, and the data load comes after in the reader's thread, so the data store happens before the data load. With the flag stored `relaxed`, there is no `releases flag_w`, and the same goal, `publish_relaxed`, fails. `hb_trans` has two terms in its trigger, since no single term mentions all three events.

Here the counterexample comes from the axioms, not the model, and this entry shows why a model is sealed. In the `timeline` model, every execution is sequentially consistent, so `hb` is just "earlier in time" and `publish_relaxed` would be true. A client sees only the axioms, and they do not prove it, because on real hardware it is false. The model shows the axioms are consistent. It is not what clients reason with. A weaker memory model, such as RC11 for `relaxed`, is a larger theory of the same shape.

## Probability

Failure budgets, retries and randomised algorithms are arguments about probabilities. Here events are abstract and `pr` gives each one a probability:

<!-- example: prob.pia -->
```ocaml
let theory Prob = sig
  let sort event
  let spec pr : (e : event) -> real
  let spec either : (a : event) -> (b : event) -> event
  let spec both : (a : event) -> (b : event) -> event
  let spec opposite : (a : event) -> event

  let axiom pr_range (e : event) ensures 0.0 <= pr e && pr e <= 1.0
  let axiom union_bound (a : event) (b : event)
    ensures pr (either a b) <= pr a + pr b
  let axiom both_le (a : event) (b : event)
    ensures pr (both a b) <= pr a && pr (both a b) <= pr b
  let axiom complement (a : event) ensures pr (opposite a) = 1.0 - pr a
end

\ An event is only its probability. `either` and `both` take the
\ worst case the axioms allow (the Fréchet bounds).
let chance = type { p : real where 0.0 <= p && p <= 1.0 }

let model bounds : Prob = struct
  let sort event = chance
  let spec pr (e : chance) : real = e.p
  let spec either (a : chance) (b : chance) : chance =
    { p = if a.p + b.p <= 1.0 then a.p + b.p else 1.0 }
  let spec both (a : chance) (b : chance) : chance =
    { p = if a.p + b.p >= 1.0 then a.p + b.p - 1.0 else 0.0 }
  let spec opposite (a : chance) : chance = { p = 1.0 - a.p }
end

let lemma request_budget (a : Prob.event) (b : Prob.event) (c : Prob.event) : unit
  requires Prob.pr a <= 0.001 && Prob.pr b <= 0.001 && Prob.pr c <= 0.001
  ensures Prob.pr (Prob.opposite (Prob.either (Prob.either a b) c)) >= 0.997
= ()
```

A request fails if any of three stages fails. Each stage's failure rate is at most one in a thousand, so `request_budget` proves that the request succeeds at least 99.7% of the time. The refinement on `chance` is what makes the model meet `pr_range`: every `chance` has `0.0 <= p && p <= 1.0`, and each of the model's functions proves it of the `chance` it returns.

**Independence is a trusted axiom.** A tighter bound, such as "two replicas both lose a write with probability at most p²", needs independence, and no deterministic random number generator is truly independent. That is the idealisation every analysis of a randomised algorithm makes, so Pia makes it visible: the axiom lives in a theory with no model, which only a `@trusted` module may declare, and its users import it with `trusting`. Trust covers the whole theory, so `Ideal` holds only the axiom that needs it.

A module cannot import another's theory yet, so this program repeats `Prob` and its model, and declares `Ideal` in the same `@trusted` file. In a library, `Ideal` would be its own module, `Pia.Rand.Ideal`, and the client would write `import Pia.Rand.Ideal trusting`.

<!-- example: ideal.pia -->
```ocaml
@trusted

let theory Prob = sig
  let sort event
  let spec pr : (e : event) -> real
  let spec either : (a : event) -> (b : event) -> event
  let spec both : (a : event) -> (b : event) -> event
  let spec opposite : (a : event) -> event

  let axiom pr_range (e : event) ensures 0.0 <= pr e && pr e <= 1.0
  let axiom union_bound (a : event) (b : event)
    ensures pr (either a b) <= pr a + pr b
  let axiom both_le (a : event) (b : event)
    ensures pr (both a b) <= pr a && pr (both a b) <= pr b
  let axiom complement (a : event) ensures pr (opposite a) = 1.0 - pr a
end

\ An event is only its probability. `either` and `both` take the
\ worst case the axioms allow (the Fréchet bounds).
let chance = type { p : real where 0.0 <= p && p <= 1.0 }

let model bounds : Prob = struct
  let sort event = chance
  let spec pr (e : chance) : real = e.p
  let spec either (a : chance) (b : chance) : chance =
    { p = if a.p + b.p <= 1.0 then a.p + b.p else 1.0 }
  let spec both (a : chance) (b : chance) : chance =
    { p = if a.p + b.p >= 1.0 then a.p + b.p - 1.0 else 0.0 }
  let spec opposite (a : chance) : chance = { p = 1.0 - a.p }
end

\ Independence is an idealisation: no model of Prob here has it (in
\ `bounds`, two events of probability 0.01 have a joint probability of
\ 0), so it is a theory of its own, trusted, and this file says so.
let theory Ideal = sig
  let spec lost : (replica : u32) -> Prob.event
  let axiom independent (i : u32) (j : u32)
    requires i <> j
    ensures Prob.pr (Prob.both (lost i) (lost j)) = Prob.pr (lost i) * Prob.pr (lost j)
end

import Ideal trusting

let lemma two_replicas : unit
  requires Prob.pr (Ideal.lost 0) <= 0.01 && Prob.pr (Ideal.lost 1) <= 0.01
  ensures Prob.pr (Prob.both (Ideal.lost 0) (Ideal.lost 1)) <= 0.0001
= ()
```

```console
$ piac --verify --trust-report --why ideal.pia
ideal.pia:37:3: the theory 'Ideal' is consistent: the solver found a witness, a model of its axioms
ideal.pia:42:1: trusting the theory 'Ideal'
ideal.pia:37:3: trusted: the axiom 'Ideal.independent', since the theory 'Ideal' has no model
  used by: ideal.pia:46:3
1 trusted item
1 of 26 proved goals rest on a trusted axiom; the other 25 are fully proved
...
26 proved, 0 failed, 0 skipped
```

`Ideal` is consistent with `Prob`'s axioms, but not with its `bounds` model, in which two events of probability 0.01 have a joint probability of 0. That is fine, because clients reason with `Prob`'s axioms and never with the model, and it is a reminder that `bounds` is a worst-case summary, not a probability space. When `Ideal` is compiled, `piac` asks Z3 whether its axioms and the `Prob` axioms they use are consistent, and finds a witness. The trust report lists `Ideal.independent`, and with `--why` the goal `two_replicas` that used it. The other goals, including `Prob`'s model check, rest on nothing trusted.

## Fail-safe control

A controller must do something safe when its inputs cannot be trusted. Which command is safe depends on the plant: a gas valve fails *closed*, a fire door fails *open*. The theory names the safe command and says it keeps a safe plant safe:

<!-- example: tank.pia -->
<!-- expect: fail -->
```ocaml
let command = type | Fill | Hold

let theory Tank = sig
  let sort plant
  let spec safe : (p : plant) -> bool
  let spec allows : (p : plant) -> (c : command) -> bool
  let spec step : (p : plant) -> (c : command) -> plant

  let axiom hold_allowed (p : plant) requires safe p ensures allows p Hold
  let axiom allowed_safe (p : plant) (c : command)
    requires safe p && allows p c
    ensures safe (step p c)
end

\ A tank that one step of filling raises by up to 10 units.
let tank = type { level : int where 0 <= level && level <= 200 }

let model levels : Tank = struct
  let sort plant = tank
  let spec safe (p : tank) : bool = p.level <= 150
  let spec allows (p : tank) (c : command) : bool =
    match c with
    | Fill -> p.level + 10 <= 150
    | Hold -> true
  let spec step (p : tank) (c : command) : tank =
    match c with
    | Fill -> { level = if p.level + 10 <= 200 then p.level + 10 else 200 }
    | Hold -> p
end

let spec decide (want : command) (sensor_ok : bool) : command =
  if sensor_ok then want else Hold

let lemma fail_closed (p : Tank.plant) (want : command) (sensor_ok : bool) : unit
  requires Tank.safe p
  requires sensor_ok ==> Tank.allows p want
  ensures Tank.safe (Tank.step p (decide want sensor_ok))
= ()

let spec decide_open (want : command) (sensor_ok : bool) : command = want

let lemma fail_open (p : Tank.plant) (want : command) (sensor_ok : bool) : unit
  requires Tank.safe p
  requires sensor_ok ==> Tank.allows p want
  ensures Tank.safe (Tank.step p (decide_open want sensor_ok))
= ()
```

```console
$ piac --verify tank.pia
...
tank.pia:37:3: proved: the postcondition holds [smt]
tank.pia:45:3: failed: the postcondition holds
  counterexample in the model 'levels': p.level = 150, want.tag = 0, sensor_ok = false
...
tank.pia:12:5: proved: the model 'levels' meets the axiom 'Tank.allowed_safe' [smt]
10 proved, 1 failed, 0 skipped
```

The controller, `decide`, passes the operator's command through when the sensor is healthy and the command is allowed, and holds otherwise, so `fail_closed` proves. A controller that keeps doing what it was told when the sensor fails, `decide_open`, which is failing open for a tank, does not.

The counterexample, found in the model, has `sensor_ok = false` and `want = Fill` (tag 0) at a level of 150, where filling would pass the safe limit and nothing says the plant allows it. The real controller in code reads integers from a sensor. It connects to the theory through an abstraction function from its readings to `Tank.plant`, defined in the model's module ([ADR 0036](adr/0036-library-theories.md#connecting-a-theory-to-code)), so its command function is proved with the same lemma.

## State machines

A protocol is a table of states and transitions, and a metaprogram can turn the table into a theory and its model, so a library describes the protocol once as data and nothing about it is trusted. The prelude's `machine` does this (step 5). Its first argument names the theory's sort, then come the type of states, the initial state and the table, one `edge` per transition. A full session proves, and sending after `shutdown` does not:

<!-- example: conn.pia -->
<!-- expect: fail -->
```ocaml
let conn_state = type | Closed | Open | Draining

let theory Conn = machine "conn" conn_state Closed
  [ edge Closed "connect" Open
  ; edge Open "send" Open
  ; edge Open "shutdown" Draining
  ; edge Draining "close" Closed ]

let lemma session (c : Conn.conn) : unit
  requires Conn.at c = Closed
  ensures Conn.at (Conn.close (Conn.shutdown (Conn.send (Conn.connect c)))) = Closed
= ()

let lemma send_after_shutdown (c : Conn.conn) : unit
  requires Conn.at c = Closed
  ensures Conn.allowed_send (Conn.shutdown (Conn.connect c))
= ()
```

```console
$ piac --verify conn.pia
...
conn.pia:11:3: proved: the postcondition holds [smt]
conn.pia:16:3: failed: the postcondition holds
  counterexample in the model 'conn_states': c.tag = 0
...
conn.pia:3:1: proved: the model 'conn_states' meets the axiom 'Conn.close_from_Draining' [smt]
10 proved, 1 failed, 0 skipped
```

`machine` is an ordinary metaprogram, written in Pia with `map` and `fold`, so it is total, as a metaprogram that builds a theory must be ([ADR 0035](adr/0035-substitution-failure-and-total-constraints.md)): what it returns becomes hypotheses of proofs. It builds an abstract sort `conn`, the state `at c` of each `c`, and a `start` in the initial state. For each event it builds an abstract function, a predicate saying where the event is allowed, and one axiom per edge saying where it leads. It also builds a model, `conn_states`, in which a `conn` is just its state, and the model proves every axiom, so nothing is trusted. The counterexample comes from that model: from `Closed` (tag 0), `connect` then `shutdown` leads to `Draining`, where `send` is not allowed. For `shutdown`, what it builds amounts to this:

<!-- example: conn_shutdown.pia -->
```ocaml
let conn_state = type | Closed | Open | Draining

let theory Conn = sig
  let sort conn
  let spec at : (c : conn) -> conn_state
  let spec shutdown : (c : conn) -> conn
  let spec allowed_shutdown : (c : conn) -> bool
  let axiom shutdown_allowed (c : conn) ensures allowed_shutdown c = (at c = Open)
  let axiom shutdown_from_Open (c : conn) requires at c = Open ensures at (shutdown c) = Draining
end

let model conn_states : Conn = struct
  let sort conn = conn_state
  let spec at (c : conn_state) : conn_state = c
  let spec shutdown (c : conn_state) : conn_state = if c = Open then Draining else c
  let spec allowed_shutdown (c : conn_state) : bool = c = Open
end
```

The generated binders are named `c#machine`, a name no source can write, and the member names (`shutdown`, `allowed_shutdown`, `shutdown_from_Open`) are kept, so clients can name them ([ADR 0022](adr/0022-metaprogram-hygiene.md)). One table builds one theory: a second `let theory` with the same call names the same theory, rather than building a second one. The library's socket API requires the event to be allowed, as in `let send (s : socket) ... requires Conn.allowed_send (abs s)`, so a program that sends after shutting down fails at the call.

A variant type and spec functions could say the same thing without a theory. The theory adds three things: the sort `conn` is abstract, so users cannot depend on how a connection is represented; the axioms are small facts rather than definitions to unfold; and one table generates the theory, its model and its proofs, for every protocol a library has. This is how [ADR 0006](adr/0006-contracts-and-module-state.md)'s module state-machine properties can be written by libraries.

## Clocks: a proof written by a tactic

Some facts about a theory need induction: one axiom says what a single step does, and a lemma says what many steps do. The proof is the same every time, the lemma calling itself one step smaller, so a tactic can write it ([ADR 0036](adr/0036-library-theories.md), step 6). A tactic is a metaprogram that `@by(...)` on a lemma runs on the lemma's goal. It returns proof steps, and the verifier proves them like steps written by hand. So a tactic can make a proof possible, but it cannot make a wrong one ([meta.md](meta.md#tactics)).

Here the theory is a clock, with one axiom: a tick adds one to the time. `ticks c n` is `n` ticks from `c`. `induction` writes the step `if n > 0 then elapsed c (n - 1)`, and with it the lemma is proved. Without the step, the same goal fails, and the report says why it may: `ticks` was unfolded only once.

<!-- example: clock.pia -->
<!-- expect: fail -->
```ocaml
let theory Clock = sig
  let sort clock
  let spec time : (c : clock) -> int
  let spec tick : (c : clock) -> clock
  let axiom tick_time (c : clock) ensures time (tick c) = time c + 1
end

let model counter : Clock = struct
  let sort clock = int
  let spec time (c : int) : int = c
  let spec tick (c : int) : int = c + 1
end

let rec spec ticks (c : Clock.clock) (n : int) : Clock.clock
  requires n >= 0
  decreases n
= if n = 0 then c else Clock.tick (ticks c (n - 1))

let meta induction (g : syntax) (on : syntax) : list =
  let args = map (let (p) => if p = name on then `( $on - 1 ) else p) (params g) in
  [ `( if $on > 0 then $(make_call (name g) args) ) ]

let lemma elapsed (c : Clock.clock) (n : int) : unit @by(induction n)
  requires n >= 0
  ensures Clock.time (ticks c n) = Clock.time c + n
  decreases n
= ()

let lemma unaided (c : Clock.clock) (n : int) : unit
  requires n >= 0
  ensures Clock.time (ticks c n) = Clock.time c + n
= ()
```

```console
$ piac --verify clock.pia
...
clock.pia:25:3: proved: the postcondition holds [smt]
clock.pia:31:23: proved: the precondition of 'ticks' holds [smt]
clock.pia:31:3: failed: the postcondition holds [the solver gave up: smt tactic failed to show goal to be sat/unsat (incomplete quantifiers)]
  hint: a recursive spec function was unfolded only as far as its @fuel allows, so this goal may hold; raise @fuel on the function or the lemma, or prove the fact by induction in a lemma
clock.pia:5:35: proved: the model 'counter' meets the axiom 'Clock.tick_time' [smt]
8 proved, 1 failed, 0 skipped
```

`induction` reads the goal's parameters with `params g`, replaces `n` with `n - 1`, and builds the call with `make_call`. It recurses on nothing, so it is total, as a tactic must be: like a theory-building metaprogram, it may not read the program, and it must terminate ([ADR 0035](adr/0035-substitution-failure-and-total-constraints.md)). The lemma still needs its `decreases n`, and the recursive call is checked against it, so a tactic that wrote a call that is not smaller would fail to prove it rather than prove the lemma wrongly. Nothing here is trusted: the model `counter`, where a clock is an integer, proves the axiom.

A theory can also choose how Z3 solves its members' goals, as in `let theory Geometry @solver(nlsat) = sig ... end` for nonlinear real arithmetic. Each member without its own `@solver` uses it. A strategy affects only how fast a goal is proved, never whether it is ([verifier.md](verifier.md#solver-strategies-and-tactics)).

## Units of measure

Adding metres to seconds is a type error in physics. Dimensions form a group, and the obvious theory, with axioms for associativity and commutativity, makes Z3 instantiate those axioms over and over. A better theory reduces a dimension to its exponents, which is linear arithmetic, and has no axiom that can loop:

<!-- example: dim.pia -->
<!-- expect: fail -->
```ocaml
let theory Dim = sig
  let sort dim
  let spec metres : (d : dim) -> int       \ the exponent of each base unit
  let spec seconds : (d : dim) -> int
  let spec kilograms : (d : dim) -> int
  let spec length : dim
  let spec time : dim
  let spec mass : dim
  let spec times : (a : dim) -> (b : dim) -> dim
  let spec per : (a : dim) -> (b : dim) -> dim

  let axiom length_exp ensures metres length = 1 && seconds length = 0 && kilograms length = 0
  let axiom time_exp ensures metres time = 0 && seconds time = 1 && kilograms time = 0
  let axiom mass_exp ensures metres mass = 0 && seconds mass = 0 && kilograms mass = 1
  let axiom times_exp (a : dim) (b : dim)
    ensures metres (times a b) = metres a + metres b
         && seconds (times a b) = seconds a + seconds b
         && kilograms (times a b) = kilograms a + kilograms b
  let axiom per_exp (a : dim) (b : dim)
    ensures metres (per a b) = metres a - metres b
         && seconds (per a b) = seconds a - seconds b
         && kilograms (per a b) = kilograms a - kilograms b
  let axiom same (a : dim) (b : dim) @trigger(metres a, metres b)
    requires metres a = metres b && seconds a = seconds b && kilograms a = kilograms b
    ensures a = b
end

let exps = type { m : int; s : int; kg : int }

let model exponents : Dim = struct
  let sort dim = exps
  let spec metres (d : exps) : int = d.m
  let spec seconds (d : exps) : int = d.s
  let spec kilograms (d : exps) : int = d.kg
  let spec length : exps = { m = 1; s = 0; kg = 0 }
  let spec time : exps = { m = 0; s = 1; kg = 0 }
  let spec mass : exps = { m = 0; s = 0; kg = 1 }
  let spec times (a : exps) (b : exps) : exps = { m = a.m + b.m; s = a.s + b.s; kg = a.kg + b.kg }
  let spec per (a : exps) (b : exps) : exps = { m = a.m - b.m; s = a.s - b.s; kg = a.kg - b.kg }
end

let lemma distance : unit
  ensures Dim.times (Dim.per Dim.length Dim.time) Dim.time = Dim.length
= ()

let lemma newton : unit
  ensures Dim.metres (Dim.per (Dim.times Dim.mass Dim.length) (Dim.times Dim.time Dim.time)) = 1
= ()

let lemma speed_is_length : unit
  ensures Dim.per Dim.length Dim.time = Dim.length
= ()
```

```console
$ piac --verify dim.pia
...
dim.pia:43:3: proved: the postcondition holds [smt]
dim.pia:47:3: proved: the postcondition holds [smt]
dim.pia:51:3: failed: the postcondition holds
  false in the model 'exponents'
...
dim.pia:25:5: proved: the model 'exponents' meets the axiom 'Dim.same' [smt]
8 proved, 1 failed, 0 skipped
```

A quantity library tags each value with a ghost `dim`, and `add` requires equal dimensions. Speed times time is a length (`distance`), and a force is a mass times a length per time squared (`newton`). Treating a speed as a length, `speed_is_length`, fails.

The lemma has no parameters, so there are no values to show: it is false in the model, where `per length time` has `seconds` -1 and `length` has 0. The `@trigger` on `same` is the one written by hand: it fires only when two dimensions' exponents are both in the query, which is when equality could matter.

## Network shapes and bounds

The worked example of [ADR 0036](adr/0036-library-theories.md#worked-example) is a theory `Lip` of neural network layers, with a `shapes` model in which a layer is its input width, output width and a Lipschitz bound. A residual block proves both its shape and `lip <= 3.0` from five axioms, and a residual around a layer whose widths differ fails at compile time. That entry also shows where trust enters: claiming that `lip` bounds the true Lipschitz constant of a kernel is a trusted axiom, and it is listed.

## Allocators

An allocator promises a few things about the blocks it hands out: a block it hands out was not live, its memory is apart from every other block's, and a block given back is dead until it is handed out again. Each allocator keeps those promises with its own data structure, such as the free stack of [tests/verify/pool.pia](https://github.com/deanberris/pia-lang/blob/main/tests/verify/pool.pia), and proving them there takes quantifiers over the pool's arrays. A theory states them once, as facts about an abstract heap, so the users of any allocator reason with small axioms instead ([ADR 0041](adr/0041-allocator-semantics-as-a-theory.md)):

<!-- example: alloc.pia -->
<!-- expect: fail -->
```ocaml
let blk = type int{0..63}

let theory Alloc = sig
  let sort heap
  let spec none : heap
  let spec live : (h : heap) -> (b : blk) -> bool
  let spec take : (h : heap) -> (b : blk) -> heap
  let spec give : (h : heap) -> (b : blk) -> heap
  let spec base : (b : blk) -> int              \ where the block's 16 bytes start

  let axiom none_live (b : blk) ensures live none b = false
  let axiom take_live (h : heap) (b : blk) (c : blk)
    ensures live (take h b) c = (c = b || live h c)
  let axiom give_live (h : heap) (b : blk) (c : blk)
    ensures live (give h b) c = (c <> b && live h c)
  let axiom apart (b : blk) (c : blk) @trigger(base b, base c)
    requires b <> c
    ensures base b + 16 <= base c || base c + 16 <= base b
end

\ The live blocks are bits of a u64, and block b is bytes 16b to 16b + 15.
let model bits : Alloc = struct
  let sort heap = u64
  let spec none : u64 = 0
  let spec live (h : u64) (b : blk) : bool = ((h >> b) & 1) = 1
  let spec take (h : u64) (b : blk) : u64 = (h | (1 << b))
  let spec give (h : u64) (b : blk) : u64 = h & ~(1 << b)
  let spec base (b : blk) : int = b * 16
end

\ A block that was not live, once taken, is apart from every live block.
let lemma fresh_apart (h : Alloc.heap) (a : blk) (b : blk) : unit
  requires Alloc.live h a && Alloc.live h b = false
  ensures Alloc.live (Alloc.take h b) a
  ensures Alloc.base a + 16 <= Alloc.base b || Alloc.base b + 16 <= Alloc.base a
= ()

\ docs/stdlib.md's reuse: take a, give it back, take b, which may be a's
\ old block. b is live, and a is dead between the give and the take.
let lemma reuse (h : Alloc.heap) (a : blk) (b : blk) : unit
  requires Alloc.live h a = false
  requires Alloc.live (Alloc.give (Alloc.take h a) a) b = false
  ensures Alloc.live (Alloc.give (Alloc.take h a) a) a = false
  ensures Alloc.live (Alloc.take (Alloc.give (Alloc.take h a) a) b) b
= ()

\ Wrong: a block given back is not live.
let lemma use_after_give (h : Alloc.heap) (a : blk) : unit
  ensures Alloc.live (Alloc.give h a) a
= ()
```

`fresh_apart` and `reuse` prove from the axioms alone, with no quantifier in sight, and `use_after_give` fails: using a block after giving it back is the use-after-free the theory exists to rule out. The `bits` model proves every axiom, so nothing is trusted.

What the theory cannot do yet is follow a running allocator. Its heap is spec-only, and code cannot hold one, so `take` and `give` in pool.pia cannot say `ensures p.heap = Alloc.take (old p.heap) result.i`. [ADR 0041](adr/0041-allocator-semantics-as-a-theory.md) proposes ghost state for that: a field or parameter the verifier sees and codegen erases. Each allocator then proves, once and privately, that its data structure matches the heap, and its users see only `Alloc`.

## Writing a theory

- **Write the model first.** If no model is easy to write, the axioms may say more than you mean. A theory without a model needs `@trusted`, and every user must import it with `trusting`. Keep trusted axioms in a theory of their own, as `Pia.Rand.Ideal` does, since trust covers a whole theory. A model can also live in another module, found by the ADL rule, which suits a theory with several implementations.
- **Prefer functions into decided theories.** The units theory maps dimensions to integers instead of stating group laws. Axioms that only relate a function's value to its arguments' values give Z3 nothing to loop on.
- **Check the triggers.** `piac --verify-stats` shows the trigger chosen for every axiom. An axiom should fire only on the terms it is about.
- **Seal on purpose.** Clients prove from the axioms only. A fact that is true in the model but not stated as an axiom is a fact clients cannot use, as the happens-before entry shows, and that is usually what you want.
- **Measure.** A theory in the standard library joins the proof benchmark (`tools/bench/corpus.txt`), so a slow axiom shows up as a resource-count regression.
