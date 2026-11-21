# The REPL

`pia repl` is an interactive Pia session. Each definition you enter joins a persistent environment, as in a Lisp REPL, and later input can use it, ask about it and redefine it. Nothing is relaxed for interactive use: a definition joins the environment only when every proof obligation in the whole environment is proved, and an expression is proved before it is compiled and run. The design is [ADR 0031](adr/0031-verified-repl-and-live-environment.md).

Build it with:

```sh
bazel build //tools/pia
alias pia="$PWD/bazel-bin/tools/pia/pia"
```

## A session

<!-- repl: session.pia -->
```ocaml
let sum (a : u8) (b : u8) : u16
  ensures result >= a
= a + b
sum 200 100
let limit : u8 = 200
let bump (a : u8) : u8 = a + 1
let bump (a : u8) : u8 requires a < 255 = a + 1
let bump (a : u8) : u8 requires a < 200 = a + 1
:redef let bump (a : u8) : u8 requires a < 200 = a + 1
bump 41
bump 250
:type sum 1 2
:env
```

Each cell is proved first. `bump` in cell 4 can overflow, so it is refused with a counterexample, and cell 5 adds the precondition that rules it out. Cell 6 tries to define `bump` again, which the no-shadowing rule forbids, so cell 7 replaces it with `:redef`. Calling `bump 250` fails its precondition at compile time, so it never runs:

```console
$ pia repl < session.pia
sum : (a : u8) -> (b : u8) -> u16  (* 2 proved *)
- : u16 = 300
limit : u8 = 200
[4]:1:28: failed: '+' does not overflow u8
  counterexample: a = 255, result = 256
[4]: error: 1 obligation failed; nothing was committed
bump : (a : u8) -> u8  (* 1 proved *)
[6]:1:1: error: 'bump' is already defined in cell [5]; Pia does not allow shadowing (ADR 0022), so name it bump' or replace it with :redef
bump : (a : u8) -> u8  (redefined)  (* 1 proved *)
- : u8 = 42
[9]:1:1: failed: the precondition of 'bump' holds
[9]: error: 1 obligation failed; nothing was committed
sum 1 2 : u16
[1] let sum : (a : u8) -> (b : u8) -> u16
[3] let limit : u8
[7] let bump : (a : u8) -> u8
```

On a terminal, `pia repl` prints a banner and reads cells with a line editor: arrows and the usual Emacs keys move and edit, Up and Down step through the history (kept in `~/.pia_history`), and Ctrl-D leaves.

## Cells

A cell is one input: Pia code, or a command that starts with `:`. Code can hold several top-level items. A definition goes on to the next line until its `=`, so a header can be followed by its contracts on the lines below, and a cell also goes on while a bracket, a comment, a string or a quote is open, or while the last line ends with a token that needs more, such as an operator, `then` or `in`. On a terminal an empty line ends a cell early. On a pipe, a cell ends where the next line starts at column 1.

Each cell is checked together with the environment, as one program:

- **Definitions** (`let`, types, `let meta` metaprograms and operators) join the environment if everything verifies. A constant's value is shown with its type.
- **Expressions** are evaluated. Each one becomes a hidden constant that is verified like any definition, so a call outside a precondition fails before anything runs. It is then compiled for the host with the ORC JIT and run, and its value is shown as `- : type = value`. Expressions do not join the environment.
- **Metaprograms run** as they do in a file: operators declared in earlier cells apply to later ones, `@derive(eq)` adds its functions, and a top-level call of a `let meta` function adds the items it returns.

A cell is a transaction. If any obligation fails, or is not proved and not accepted with `:allow`, nothing in the cell is committed, and the failures are shown with their counterexamples. So the environment is always a program that verifies.

Locations are written `[cell]:line:col`, counting lines within the cell.

## Redefinition

Pia has no shadowing ([ADR 0022](adr/0022-metaprogram-hygiene.md)), and the REPL keeps that rule: defining a name that already exists is an error that suggests a primed name such as `bump'`. To replace a definition, use `:redef`. The new definition is checked in place of the old one together with everything else, so each definition that uses it is proved again against the new one. If any of those proofs breaks, the redefinition is refused, and nothing changes.

`:forget name` removes a definition the same way. It is refused while anything still uses it.

A name that a metaprogram call generated belongs to that call: redefine the call instead.

## Live redefinition

`:spawn <expr>` proves an expression, then runs it on a thread of its own, so the session carries on while it runs. Redefining a function the task uses swaps the new code into the running task, as in Lisp, as long as the change is proved safe for code that is already running ([ADR 0031](adr/0031-verified-repl-and-live-environment.md)):

- **Every definition is called through a slot.** In the REPL, a call from one definition to another loads the callee's current code from its slot. Committing a redefinition stores the new code in the slot, so each call that starts afterwards runs it, while calls already running finish on the code they started in. The engine holding old code stays alive until no task uses it.
- **A refinement swaps at once.** The task's code was proved against the old definition's contract. So the new definition's body is proved against that old contract as well as its own, as a hidden function: its obligations under the old `requires`, and the old `ensures`. If that proof holds and the type is unchanged, the swap is safe for the running task wherever it is, and the result says `swapped into running task 1`.
- **Any other change swaps together with its callers.** If the new body does not meet the old contract, or its type changed (also when a record type it uses changed), the code that calls it was proved against something that no longer holds. The redefinition and everything that uses it are verified again, as always, and then the changed definition and every definition that calls it are swapped together, at a moment when no task is running any of them. Calls into that set from outside it wait while the set drains, for at most two seconds. Their callers outside the set relied only on contracts that did not change, so they carry on. If a task never leaves the set, for example because its own expression calls a definition in it, nothing is committed until the task finishes.
- **Everything else is the same as without tasks.** Definitions no running task can reach change freely. `:forget` and `:reset` wait for the tasks that need what they would remove.

To find that moment, code that a task may run counts its calls in progress, one counter per definition. That costs a few nanoseconds per call, so the REPL counts only in code compiled while a task runs or for `:spawn`. Compiled programs never count.

<!-- repl: live.pia -->
```ocaml
let step (a : u64) : u64
  requires a < 1000
  ensures result = 1
= 1
let total (n : u64) : u64
  requires n <= 8000000000
= let s : mutable u64 = 0 in
  for i in 0 .. n
    invariant s <= 2 * i
  do s <- s + step 5 done;
  s
:spawn total 1000000000
:redef let step (a : u64) : u64 requires a < 1000 ensures result = 1 = 2 - 1
:redef let step (a : u64) : u64 requires a < 1000 ensures result <= 2 = 2
:wait 1
```

```console
$ pia repl < live.pia
step : (a : usize) -> usize  (* 1 proved *)
total : (n : usize) -> usize  (* 4 proved *)
task 1 (total 1000000000) running
step : (a : usize) -> usize  (redefined, swapped into running task 1)  (* 2 proved *)
[5]: error: 'step' no longer refines what running code was proved against (the new body does not meet the old contract: the postcondition holds (the old contract at [4]:1:44)), so it can only be swapped together with 'total', which calls it, at a moment when no task is running any of them, but task 1 stayed inside 'total' for 2000 ms; nothing was committed (wait for the task with :wait)
task 1 (total 1000000000) done: usize = 1000000000
```

The second `step` would still let `total` verify, but `total` was proved against `result = 1`, and the task never leaves `total`, so the change waits for it. With one more level of calls, the same change goes through while the task runs:

<!-- untested: the final value depends on when the swap happens -->
```ocaml
let chunk (k : u64) : u64
  requires k <= 1000
  ensures result <= 2 * k
= let s : mutable u64 = 0 in
  for i in 0 .. k
    invariant s <= 2 * i
  do s <- s + step 5 done;
  s
let many (n : u64) : u64
  requires n <= 8000000
= let s : mutable u64 = 0 in
  for i in 0 .. n
    invariant s <= 2000 * i
  do s <- s + chunk 1000 done;
  s
:spawn many 1000000
:redef let step (a : u64) : u64 requires a < 1000 ensures result <= 2 = 2
:wait 2
```

```console
task 2 (many 1000000) running
step : (a : usize) -> usize  (redefined, swapped into running task 2 at a moment when no task was running 'chunk' or 'step')  (* 1 proved *)
task 2 (many 1000000) done: usize = 1497312000
```

`chunk` still verifies with the new `step`, and `many` relies only on `chunk`'s contract, which did not change. So `step` and `chunk` are swapped together between two calls of `chunk`. Every call of `chunk` ran wholly on the old code or wholly on the new, which is why the value is a multiple of 1000.

### Metaprograms that change the environment

The REPL gives metaprograms the environment as data, through `Pia.Live`: `listing ()` lists every definition, and `redefine x` turns the definitions in the syntax `x` into replacements ([metaprograms](meta.md#comments-and-literate-programs)). A metaprogram's changes take exactly the same path as a `:redef` cell, so nothing it does can install code that is not proved, and a definition a running task uses is swapped in only if it refines the old one:

```ocaml
let meta faster () =
  redefine `( let step ($!a : u64) : u64 requires $!a < 1000 ensures $!result = 1 = 1 + 0 )
```

`Pia.Live` exists only in the REPL. `piac` refuses `redefine`, and compiled programs call functions directly, with no slots.

## State

A `let` with no parameters whose type says `mutable` is a *state*: a value that persists from cell to cell, which definitions can read and change ([ADR 0031](adr/0031-verified-repl-and-live-environment.md)). Its `invariant` is a fact that every definition must keep:

<!-- repl: state.pia -->
```ocaml
let count : mutable u8
  invariant count <= 100
= 0
let bump () : unit = if count < 100 then count <- count + 1 else ()
bump ()
bump ()
count
let tick () : unit = count <- count + 1
:redef let count : mutable u16 invariant count <= 1000 = old count * 10
count
```

```console
$ pia repl < state.pia
count : mutable u8 = 0  (* 1 proved *)
bump : () -> unit  (* 5 proved *)
- : unit = ()
- : unit = ()
- : u8 = 2
[1]:2:19: failed: the postcondition holds
[6]: error: 1 obligation failed; nothing was committed
count : mutable u16 = 20  (redefined, migrated from mutable u8)  (* 3 proved *)
- : u16 = 20
```

`tick` could take `count` past 100, so it is refused, and the failure points at the invariant it would break.

- **How it is proved.** Every definition that uses a state, directly or through a call, takes it as a `borrowed inout mutable` one-element buffer, so the verifier treats it like any other buffer. Each such definition requires the invariant and ensures it, every loop in it has the invariant as a loop invariant, and a definition that never writes the state ensures it is unchanged. The initial value is proved to meet the invariant. Since an invariant holds whenever no call is in progress, a redefinition of a function that uses a state keeps the invariant too: its contract includes it.
- **Migration.** `:redef` of a state starts it again from its new initial value, unless the value names `old count`, the value of the definition it replaces. Then the new value is computed from the old one, and proved to meet the new type and the new invariant for every old value the old invariant allows. Above, `old count * 10` fits in `u16` and stays at most 1000 because the old `count` is at most 100. Going back to `u8` with `old count` would be refused, since `old count` may be 1000.
- **Tasks.** A state that a running task uses belongs to the task until it finishes. Reading it, writing it, redefining it or forgetting it waits for the task, so a task and the session never race on it. Functions that use it can still be redefined while the task runs, as above: a new body that keeps the old contract, and with it the invariant, is swapped into the task.
- **Cells.** A cell can be a statement, such as `count <- 7`, and its result is checked against the invariant like any definition's.

A state is an integer or a `bool` for now. State belongs to the REPL until modules ([M8](https://github.com/deanberris/pia-lang/issues/9)) bring module state to compiled programs, so `piac` refuses an `invariant` on a definition.

## Commands

| Command | |
| --- | --- |
| `:type <expr>` | the type of an expression, or of a definition |
| `:proof [<name>]` | a definition's obligations and how each was proved, or a summary of all of them |
| `:env` | the environment's definitions, with the cell each came from |
| `:source <name>` | a definition's source |
| `:redef <code>` | replace the definitions of the names `code` defines |
| `:forget <name>` | remove a definition that nothing uses |
| `:allow [<spec>]` | accept unproved obligations in a function, or at `[cell]:line[:col]`; with no argument, list what is accepted |
| `:spawn <expr>` | run an expression as a background task (see [Live redefinition](#live-redefinition)) |
| `:tasks` | the tasks, running or done, with their values |
| `:wait <n>` | wait for task `n` to finish, and show its value |
| `:load <file>` | run a file as one cell; for a literate `.pia.md` file, its `pia` blocks |
| `:reset` | empty the environment |
| `:help` | the list of commands |
| `:quit` | leave |

`pia repl` takes the same `--allow-unproved=<spec>` flag as `piac`, and `--meta-cycles=N`, `--timeout-ms=N` (the solver's limit per obligation) and `--no-run` (verify, but never compile or run). Files named on the command line are loaded first, each as one cell.

## JSON output

`pia repl --json` reads one JSON request per line and writes one JSON result per line, for scripts and tools. A request:

```json
{"id": 1, "code": "let sum (a : u8) (b : u8) : u16 = a + b"}
```

and its result, broken over lines here:

```json
{"cell": 1, "events": [
  {"kind": "proof", "method": "intervals", "name": "sum", "status": "proved", "text": "'+' does not overflow u16", "where": {"cell": 1, "column": 37, "line": 1}},
  {"kind": "defined", "name": "sum", "type": "(a : u8) -> (b : u8) -> u16"}], "id": 1, "ok": true}
```

`id` is copied from the request, if it has one. `--input=text` and `--output=json` mix the two: cells read as text, results written as JSON.

Each event has a `kind`:

| Kind | Fields | |
| --- | --- | --- |
| `defined`, `redefined` | `name`, `type`, `value`, `text` | a definition joined the environment; `value` for a constant; `type` is `type`, `meta` or `operator` for those items; `text` says which running tasks a redefinition was swapped into |
| `removed` | `name` | `:forget` removed it |
| `value` | `type`, `value` | an expression's value |
| `type` | `text`, `type` | `:type`'s answer |
| `proof` | `name`, `status`, `text`, `method`, `counterexample`, `where` | one obligation: `status` is `proved`, `failed`, `unproved` or `allowed`, `text` the claim, `counterexample` an object of names and values |
| `error` | `text`, `where` | |
| `info` | `text` | command output and notes |
| `task` | `name`, `text`, `type`, `status`, `value` | a background task: `name` is its number, `text` its expression, `status` `running` or `done`, and `value` its value once done |

`where` is `{"cell", "line", "column"}`. The exit status is 1 if any cell failed.

## MCP server

`pia mcp` serves a persistent REPL session over the Model Context Protocol (stdio transport), so an agent such as Claude can use Pia interactively. It has exactly two tools, in the style of Code Mode:

- **`execute {code, wait_ms?, json?}`** runs a cell, code or a command, in the session. It waits up to `wait_ms` (10 seconds by default) and returns the cell's result as the text `pia repl` prints. A cell that is still running returns its job number instead.
- **`poll {job, wait_ms?, json?}`** waits for a job and returns its state (`queued`, `running` or `done`) and, once it is done, its result.

With `json: true`, a result also carries the job, its state and the JSON result above as structured content. It is off by default because some clients, Claude Code among them, show the agent the structured content in place of the text, and the events are several times longer than the text.

A tool result is an error when the cell failed, so the agent sees failed proofs and counterexamples as errors to fix. To use it from Claude Code:

```sh
claude mcp add pia -- "$PWD/bazel-bin/tools/pia/pia" mcp
```

## The session API

Every front end is a thin layer over two C++ classes in `src/repl`, so the planned Jupyter kernel ([#64](https://github.com/deanberris/pia-lang/issues/64)) will share them too:

- **`pia::repl::Session`** holds the environment. `execute(cell)` runs one cell and returns a `CellResult`: its number, whether it succeeded, and its events. `render` turns that into the text `pia repl` prints and `toJson` into the JSON above. `Session::isComplete(text)` tells a front end whether a cell needs more lines.
- **`pia::repl::Kernel`** runs a session on a worker thread. `submit(cell)` queues a cell and returns a job number; `poll(job, wait)` returns its state, and its result once it is done. Jobs run one at a time, in order.

Neither is part of the Pia runtime. Compiled programs never contain the session, the JIT or the environment.

## Limits

- Each cell verifies and compiles the whole environment again. That is quick for interactive sizes; caching proofs per definition is planned.
- Values of integer, `bool`, `unit` and record types can be shown. Arrays and slices cannot be returned yet, so they cannot be shown either.
- Everything [not compiled yet](status.md#known-limitations) is not available in the REPL either.
- A task cannot be stopped before it finishes. Its termination is proved, but that does not bound how long it takes.
- Swaps happen one definition at a time. A change to a group of definitions that a running task uses is accepted only if each one refines its old contract. A change to a type, or to a function's type, waits for the tasks that use it: migrating live values to a new layout is designed but not built.
- Tasks have no I/O yet, so the only thing they produce is their value.
