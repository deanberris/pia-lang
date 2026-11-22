# A catalogue of theories

A *theory* teaches the verifier about a domain. It declares new sorts, functions on them that have no body, and axioms about them, and it lives in a library, not in the compiler ([ADR 0036](adr/0036-library-theories.md)). This page is a catalogue of worked theories. Each one shows the theory, a model that proves its axioms, a proof that uses the theory, and a mistake that the theory catches.

!!! note "Status"
    Theories are designed but not implemented yet. Each example below is marked `untested` and is skipped by the documentation test. When the implementation step that an example needs lands (the table below says which), its marker comes off and the example is proved by `piac --verify` in CI like every other example on these pages.

## How to read an entry

Every theory has the same four parts.

1. **The theory.** A `sig` of sorts (`let sort`), abstract spec functions (`let spec` with no body) and axioms (`let axiom`). Everything in it is spec-only: it can appear in contracts, spec functions and lemmas, and codegen erases it.
2. **The model.** A `struct` that gives each sort a concrete type and each function a definition, so that every axiom becomes a lemma the solver proves. A theory with a proved model cannot contradict itself, so its axioms cannot make the verifier accept a false goal. Then the model is sealed: code that imports the theory sees the axioms, never the model.
3. **A proof that uses it.** A lemma or a function contract that the axioms prove.
4. **A mistake it catches.** A version that is wrong and fails with a counterexample.

An entry also says whether anything in it is **trusted**. A trusted theory has no model that the program can find, so it is declared in a `@trusted` module and imported with `trusting`. Trust covers the whole theory, and the compiler lists every axiom it brings in `piac --trust-report`.

| Theory | What it proves | Trusted | Tested from |
| --- | --- | --- | --- |
| [Lock levels](#lock-levels) | a lock discipline rules out lock-order deadlock | nothing | step 3 |
| [Happens-before](#happens-before-and-memory-orders) | release/acquire publishes data, relaxed does not | nothing | step 3 |
| [Probability](#probability) | union bounds on failure; independence as an explicit trust | `independent` only | steps 3 and 4 |
| [Fail-safe control](#fail-safe-control) | a controller falls back to a safe command on a sensor fault | nothing | step 3 |
| [State machines](#state-machines) | a protocol is followed, from a table of transitions | nothing | step 5 |
| [Units of measure](#units-of-measure) | quantities are combined with the right dimensions | nothing | step 3 |
| [Network shapes and bounds](#network-shapes-and-bounds) | layer shapes match and Lipschitz bounds compose | nothing | step 3 |

The steps are the implementation order of ADR 0036: (1) spec-only `real` and `int`, (2) theories in `@trusted` modules, (3) models and sealing, (4) certificates and `trusting`, (5) theory-building metaprograms.

## Lock levels

[ADR 0027](adr/0027-coroutines-and-race-freedom.md) rules out lock-order deadlock with static lock levels: a task may only take a lock above every level it holds. The compiler checks Pia's own `mutex` that way. A library with its own lock discipline, such as a database lock manager or a kernel's spinlock hierarchy, can state the same rule as a theory, and the verifier then checks it in that library's users.

`held` is the set of levels a task holds, and `below h n` says every held level is less than `n`:

<!-- untested: theories land in ADR 0036 step 3 -->
```ocaml
let level = int{0..63}

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
  let axiom below_held (h : held) (n : level) (m : level)
    requires below h n && holds h m
    ensures m < n
end

\ Levels are bits of a u64: bit n is set when level n is held.
let model bits : Levels = struct
  let sort held = u64
  let spec none : u64 = 0
  let spec take (h : u64) (n : level) : u64 = h | (1 << n)
  let spec drop (h : u64) (n : level) : u64 = h & ~(1 << n)
  let spec holds (h : u64) (n : level) : bool = ((h >> n) & 1) = 1
  let spec below (h : u64) (n : level) : bool = (h >> n) = 0
end
```

The model's obligations are bit-vector facts, such as `(h >> n) = 0 && n < m ==> ((h | (1 << n)) >> m) = 0`, which Z3 decides.

A lock manager's `acquire` takes the task's held set as a ghost argument and requires the new level to be above it, and its users prove their own lock orders from the axioms:

<!-- untested: theories land in ADR 0036 step 3 -->
```ocaml
import Levels

\ accounts are level 2 and the ledger is level 3
let lemma transfer_order (h : Levels.held) : unit
  requires Levels.below h 2
  ensures Levels.below (Levels.take h 2) 3
= ()
```

Taking the ledger first and then an account is the deadlock the rule exists to prevent, and it fails:

<!-- untested: theories land in ADR 0036 step 3 -->
<!-- expect: fail -->
```ocaml
import Levels

let lemma ledger_then_account (h : Levels.held) : unit
  requires Levels.below h 3
  ensures Levels.below (Levels.take h 3) 2
= ()
```

The counterexample holds level 3, and `below_held` says a held level must be below 2.

## Happens-before and memory orders

[ADR 0027](adr/0027-coroutines-and-race-freedom.md) counts a happens-before edge from atomics only when the memory orders create one: a `release` store read by an `acquire` load. The usual bug is publishing data with a flag written `relaxed`. As a theory, the rule is four axioms over events:

<!-- untested: theories land in ADR 0036 step 3 -->
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
  let axiom hb_trans (a : event) (b : event) (c : event)
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
```

The message-passing idiom proves: the data store is before the flag's release store in its thread, the flag's acquire load reads it, and the data load comes after in the reader's thread, so the data store happens before the data load.

<!-- untested: theories land in ADR 0036 step 3 -->
```ocaml
import Order

let lemma publish (data_w : Order.event) (flag_w : Order.event)
                  (flag_r : Order.event) (data_r : Order.event) : unit
  requires Order.po data_w flag_w && Order.releases flag_w
  requires Order.rf flag_w flag_r && Order.acquires flag_r
  requires Order.po flag_r data_r
  ensures Order.hb data_w data_r
= ()
```

With the flag stored `relaxed`, there is no `releases flag_w`, and the same goal fails:

<!-- untested: theories land in ADR 0036 step 3 -->
<!-- expect: fail -->
```ocaml
import Order

let lemma publish_relaxed (data_w : Order.event) (flag_w : Order.event)
                          (flag_r : Order.event) (data_r : Order.event) : unit
  requires Order.po data_w flag_w
  requires Order.rf flag_w flag_r && Order.acquires flag_r
  requires Order.po flag_r data_r
  ensures Order.hb data_w data_r
= ()
```

This entry shows why a model is sealed. In the `timeline` model, every execution is sequentially consistent, so `hb` is just "earlier in time" and `publish_relaxed` would be true. A client sees only the axioms, and they do not prove it, because on real hardware it is false. The model shows the axioms are consistent. It is not what clients reason with. A weaker memory model, such as RC11 for `relaxed`, is a larger theory of the same shape.

## Probability

Failure budgets, retries and randomised algorithms are arguments about probabilities. Here events are abstract and `pr` gives each one a probability:

<!-- untested: theories land in ADR 0036 step 3 -->
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
```

A request fails if any of three stages fails. Each stage's failure rate is at most one in a thousand, so the request succeeds at least 99.7% of the time:

<!-- untested: theories land in ADR 0036 step 3 -->
```ocaml
import Prob

let lemma request_budget (a : Prob.event) (b : Prob.event) (c : Prob.event) : unit
  requires Prob.pr a <= 0.001 && Prob.pr b <= 0.001 && Prob.pr c <= 0.001
  ensures Prob.pr (Prob.opposite (Prob.either (Prob.either a b) c)) >= 0.997
= ()
```

**Independence is a trusted axiom.** A tighter bound, such as "two replicas both lose a write with probability at most p²", needs independence, and no deterministic random number generator is truly independent. That is the idealisation every analysis of a randomised algorithm makes, so Pia makes it visible: the axiom lives in a `@trusted` module, and its users must import that theory with `trusting`. Trust covers the whole theory, so `Ideal` holds only the axiom that needs it.

<!-- untested: trusted theories and `trusting` land in ADR 0036 step 4 -->
```ocaml
(* Pia.Rand.Ideal, @trusted *)
import Prob

let theory Ideal = sig
  let spec lost : (replica : u32) -> Prob.event
  let axiom independent (i : u32) (j : u32)
    requires i <> j
    ensures Prob.pr (Prob.both (lost i) (lost j)) = Prob.pr (lost i) * Prob.pr (lost j)
end
```

<!-- untested: trusted theories and `trusting` land in ADR 0036 step 4 -->
```ocaml
import Prob
import Pia.Rand.Ideal trusting

let lemma two_replicas : unit
  requires Prob.pr (Ideal.lost 0) <= 0.01 && Prob.pr (Ideal.lost 1) <= 0.01
  ensures Prob.pr (Prob.both (Ideal.lost 0) (Ideal.lost 1)) <= 0.0001
= ()
```

`Ideal` is consistent with `Prob`'s axioms, but not with its `bounds` model, in which two events of probability 0.01 have a joint probability of 0. That is fine, because clients reason with `Prob`'s axioms and never with the model, and it is a reminder that `bounds` is a worst-case summary, not a probability space. When `Ideal` is compiled, `piac` asks Z3 whether its axioms and `Prob`'s are consistent, and records the model Z3 finds as a witness. The trust report lists `Pia.Rand.Ideal.independent` and, with `--why`, the goal `two_replicas` that used it.

## Fail-safe control

A controller must do something safe when its inputs cannot be trusted. Which command is safe depends on the plant: a gas valve fails *closed*, a fire door fails *open*. The theory names the safe command and says it keeps a safe plant safe:

<!-- untested: theories land in ADR 0036 step 3 -->
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
```

The controller passes the operator's command through when the sensor is healthy and the command is allowed, and holds otherwise. It fails closed:

<!-- untested: theories land in ADR 0036 step 3 -->
```ocaml
import Tank

let spec decide (want : command) (sensor_ok : bool) : command =
  if sensor_ok then want else Hold

let lemma fail_closed (p : Tank.plant) (want : command) (sensor_ok : bool) : unit
  requires Tank.safe p
  requires sensor_ok ==> Tank.allows p want
  ensures Tank.safe (Tank.step p (decide want sensor_ok))
= ()
```

A controller that keeps doing what it was told when the sensor fails, which is failing open for a tank, does not prove:

<!-- untested: theories land in ADR 0036 step 3 -->
<!-- expect: fail -->
```ocaml
import Tank

let spec decide_open (want : command) (sensor_ok : bool) : command = want

let lemma fail_open (p : Tank.plant) (want : command) (sensor_ok : bool) : unit
  requires Tank.safe p
  requires sensor_ok ==> Tank.allows p want
  ensures Tank.safe (Tank.step p (decide_open want sensor_ok))
= ()
```

The counterexample has `sensor_ok = false` and `want = Fill`, where nothing says the plant allows filling. The real controller in code reads integers from a sensor. It connects to the theory through an abstraction function from its readings to `Tank.plant`, defined in the model's module ([ADR 0036](adr/0036-library-theories.md#connecting-a-theory-to-code)), so its command function is proved with the same lemma.

## State machines

A protocol is a table of states and transitions, and a metaprogram can turn the table into a theory and its model, so a library describes the protocol once as data and nothing about it is trusted. This uses theory-building metaprograms (step 5):

<!-- untested: theory-building metaprograms land in ADR 0036 step 5 -->
```ocaml
let conn_state = type | Closed | Open | Draining

let theory Conn = machine conn_state Closed
  [ edge Closed "connect" Open
  ; edge Open "send" Open
  ; edge Open "shutdown" Draining
  ; edge Draining "close" Closed ]
```

`machine` generates, for each event, an abstract function on an abstract sort `conn`, a predicate saying where the event is allowed, and an axiom saying where it leads. For `shutdown`, it generates:

<!-- untested: theories land in ADR 0036 step 3 -->
```ocaml
let conn_state = type | Closed | Open | Draining

let theory Conn = sig
  let sort conn
  let spec at : (c : conn) -> conn_state
  let spec shutdown : (c : conn) -> conn
  let spec allowed_shutdown : (c : conn) -> bool
  let axiom shutdown_allowed (c : conn) ensures allowed_shutdown c = (at c = Open)
  let axiom shutdown_at (c : conn) requires at c = Open ensures at (shutdown c) = Draining
end

let model states : Conn = struct
  let sort conn = conn_state
  let spec at (c : conn_state) : conn_state = c
  let spec shutdown (c : conn_state) : conn_state = if c = Open then Draining else c
  let spec allowed_shutdown (c : conn_state) : bool = c = Open
end
```

It writes the other events the same way. The library's socket API requires the event to be allowed, as in `let send (s : socket) ... requires Conn.allowed_send (abs s)`, so a program that sends after shutting down fails at the call. As lemmas, a full session proves, and sending after `shutdown` does not:

<!-- untested: theory-building metaprograms land in ADR 0036 step 5 -->
```ocaml
import Conn

let lemma session (c : Conn.conn) : unit
  requires Conn.at c = Closed
  ensures Conn.at (Conn.close (Conn.shutdown (Conn.send (Conn.connect c)))) = Closed
= ()
```

<!-- untested: theory-building metaprograms land in ADR 0036 step 5 -->
<!-- expect: fail -->
```ocaml
import Conn

let lemma send_after_shutdown (c : Conn.conn) : unit
  requires Conn.at c = Closed
  ensures Conn.allowed_send (Conn.shutdown (Conn.connect c))
= ()
```

A variant type and spec functions could say the same thing without a theory. The theory adds three things: the sort `conn` is abstract, so users cannot depend on how a connection is represented; the axioms are small facts rather than definitions to unfold; and one table generates the theory, its model and its proofs, for every protocol a library has. This is how [ADR 0006](adr/0006-contracts-and-module-state.md)'s module state-machine properties can be written by libraries.

## Units of measure

Adding metres to seconds is a type error in physics. Dimensions form a group, and the obvious theory, with axioms for associativity and commutativity, makes Z3 instantiate those axioms over and over. A better theory reduces a dimension to its exponents, which is linear arithmetic, and has no axiom that can loop:

<!-- untested: theories land in ADR 0036 step 3 -->
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
  let axiom same (a : dim) (b : dim)
    requires metres a = metres b && seconds a = seconds b && kilograms a = kilograms b
    ensures a = b
    @trigger(metres a, metres b)
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
```

A quantity library tags each value with a ghost `dim`, and `add` requires equal dimensions. Speed times time is a length, and a force is a mass times a length per time squared:

<!-- untested: theories land in ADR 0036 step 3 -->
```ocaml
import Dim

let lemma distance : unit
  ensures Dim.times (Dim.per Dim.length Dim.time) Dim.time = Dim.length
= ()

let lemma newton : unit
  ensures Dim.metres (Dim.per (Dim.times Dim.mass Dim.length) (Dim.times Dim.time Dim.time)) = 1
= ()
```

Treating a speed as a length fails:

<!-- untested: theories land in ADR 0036 step 3 -->
<!-- expect: fail -->
```ocaml
import Dim

let lemma speed_is_length : unit
  ensures Dim.per Dim.length Dim.time = Dim.length
= ()
```

The counterexample is just the exponents: `seconds` is -1 on one side and 0 on the other. The `@trigger` on `same` is the one written by hand: it fires only when two dimensions' exponents are both in the query, which is when equality could matter.

## Network shapes and bounds

The worked example of [ADR 0036](adr/0036-library-theories.md#worked-example) is a theory `Lip` of neural network layers, with a `shapes` model in which a layer is its input width, output width and a Lipschitz bound. A residual block proves both its shape and `lip <= 3.0` from five axioms, and a residual around a layer whose widths differ fails at compile time. That entry also shows where trust enters: claiming that `lip` bounds the true Lipschitz constant of a kernel is a trusted axiom, and it is listed.

## Writing a theory

- **Write the model first.** If no model is easy to write, the axioms may say more than you mean. A theory without a model needs `@trusted`, and every user must import it with `trusting`. Keep trusted axioms in a theory of their own, as `Pia.Rand.Ideal` does, since trust covers a whole theory. A model can also live in another module, found by the ADL rule, which suits a theory with several implementations.
- **Prefer functions into decided theories.** The units theory maps dimensions to integers instead of stating group laws. Axioms that only relate a function's value to its arguments' values give Z3 nothing to loop on.
- **Check the triggers.** `piac --verify-stats` shows the trigger chosen for every axiom. An axiom should fire only on the terms it is about.
- **Seal on purpose.** Clients prove from the axioms only. A fact that is true in the model but not stated as an axiom is a fact clients cannot use, as the happens-before entry shows, and that is usually what you want.
- **Measure.** A theory in the standard library joins the proof benchmark (`tools/bench/corpus.txt`), so a slow axiom shows up as a resource-count regression.
