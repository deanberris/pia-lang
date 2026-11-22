---
name: pia-repl
description: Run Pia cells through `pia repl` from a shell, as piped text or JSON lines, including redefinition, REPL state with invariants and `old` migration, and background tasks. Use when you need a verified Pia session without an MCP connection, or want a session saved as a file and replayed as a test.
---

# Using `pia repl` from a shell

`pia repl` is a persistent Pia environment where a definition joins only if every obligation in the whole environment is proved. Each input is a *cell*, and a cell is a transaction: if anything in it fails, nothing in it is committed. The full reference is [docs/repl.md](../../docs/repl.md) and the design is ADR 0031.

```sh
bazel build //tools/pia
pia=bazel-bin/tools/pia/pia
```

## Three ways to feed it

| Mode | Command | Use it for |
| --- | --- | --- |
| text on a pipe | `pia repl < session.pia` | replaying a session file; the output is what the MCP server would return, cell by cell |
| JSON lines | `pia repl --json` | scripts: one request `{"id": 1, "code": "..."}` per line in, one result per line out |
| mixed | `pia repl --input=text --output=json` | a session file in, machine-readable results out |

Files named on the command line are loaded first, each as one cell: `pia repl lib.pia < cells.pia`. The exit status is 1 if any cell failed (on a pipe or with JSON input), so a session file works as a test.

Other flags: `--no-run` (verify, never compile or run), `--allow-unproved=<spec>` (as for piac), `--timeout-ms=N` (the solver's limit per obligation) and `--meta-cycles=N`.

### Where a cell ends on a pipe

A cell ends where the next line starts at column 1. A definition also goes on to the next line until its `=`, so this is one cell:

<!-- untested: layout illustration; the sessions below are checked -->
```ocaml
let clamp (lo : u8) (hi : u8) (x : u8) : u8
  requires lo <= hi
  ensures lo <= result && result <= hi
= if x < lo then lo
  else if x > hi then hi
  else x
```

Indent every line of a body after its first. A cell also goes on while a bracket, comment, string or quote is open, or while a line ends with a token that needs more (an operator, `then`, `in`).

### JSON results

A failed cell, broken over lines here:

```json
{"cell": 1, "events": [
  {"counterexample": {"a": "255", "result": "256"}, "kind": "proof", "method": "counterexample", "name": "bump", "status": "failed", "text": "'+' does not overflow u8", "where": {"cell": 1, "column": 28, "line": 1}},
  {"kind": "error", "text": "1 obligation failed; nothing was committed", "where": {"cell": 1, "column": 0, "line": 0}}],
 "id": 1, "ok": false}
```

Counterexample values are strings, since they can exceed 64 bits. Look at `ok` first, then the `proof` events whose `status` is `failed` or `unproved`. Event kinds are `defined`, `redefined`, `removed`, `value`, `type`, `proof`, `error`, `info` and `task`; [docs/repl.md](../../docs/repl.md#json-output) lists their fields.

## Commands

| Command | |
| --- | --- |
| `:type <expr>` | the type of an expression or definition |
| `:proof [<name>]` | a definition's obligations and how each was proved, or a summary |
| `:env` | definitions with the cell each came from |
| `:source <name>` | a definition's source |
| `:redef <code>` | replace definitions; everything that uses them is proved again |
| `:forget <name>` | remove a definition nothing uses |
| `:allow [<spec>]` | accept unproved obligations in a function or at `[cell]:line[:col]`; no argument lists them |
| `:spawn <expr>`, `:tasks`, `:wait <n>` | background tasks |
| `:load <file>` | a `.pia` file, or a `.pia.md` file's `pia` blocks, as one cell |
| `:reset` | empty the environment |

## Redefinition

Pia has no shadowing, so `let bump` twice is an error that suggests `bump'`. Use `:redef let bump ...`. The new definition is checked in place of the old one together with everything else, so it is refused if any user of `bump` no longer proves, and the failure is reported at that user's call.

## State with an invariant

A parameterless `let` whose type is `mutable` is state that persists across cells. Its `invariant` must hold after every definition that touches it, and is assumed on entry:

<!-- repl: state_skill.pia -->
```ocaml
let level : mutable u8
  invariant level <= 10
= 0
let raise () : unit = if level < 10 then level <- level + 1 else ()
raise ()
level
let force () : unit = level <- level + 1
:redef let level : mutable u16 invariant level <= 100 = old level * 10
level
```

```console
$ pia repl < state_skill.pia
level : mutable u8 = 0  (* 1 proved *)
raise : () -> unit  (* 5 proved *)
- : unit = ()
- : u8 = 1
[1]:2:19: failed: the postcondition holds
[5]: error: 1 obligation failed; nothing was committed
level : mutable u16 = 10  (redefined, migrated from mutable u8)  (* 3 proved *)
- : u16 = 10
```

- `force` could take `level` past 10, so it fails at the invariant (the location is the invariant's line in cell 1).
- `:redef` of a state restarts it from the new initial value, unless the value mentions `old level`. Then it is a migration, proved for every old value the old invariant allows. Here `old level * 10` is at most 100.
- State is an integer or `bool` for now, and exists only in the REPL: `piac` refuses `invariant` on a definition.

## Background tasks and live redefinition

`:spawn total 1000000000` proves the expression and runs it on its own thread. While it runs:

- A `:redef` of a function the task uses is swapped in at once if the new body also meets the **old** contract and the type is unchanged (`swapped into running task 1`).
- Otherwise the changed function and all its callers are swapped together at a moment when no task is inside any of them, waiting at most two seconds. If the task never leaves them, the redefinition is refused; `:wait` for the task and try again.
- State a task uses belongs to the task until it finishes.

`:wait n` shows the task's value. A task cannot be stopped early, and has no I/O yet.

## Saving a session as a test

A session that settled a question is worth keeping. Put the cells in a `<!-- repl: name.pia -->` ` ```ocaml ` block in a docs page, followed by a ` ```console ` block that starts with `$ pia repl < name.pia` and holds the output. `//tests/docs:doc_examples_test` replays it and fails if the output drifts. A line `...` in the expected output matches any number of lines.
