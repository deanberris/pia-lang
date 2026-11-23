---
name: pia-mcp
description: Drive a Pia REPL session through the `pia mcp` server's two tools, execute and poll. Use when an MCP server named pia (or tools named execute/poll from pia-repl) is connected and you want to prove, run, redefine or explore Pia code cell by cell.
---

# Driving Pia through `pia mcp`

`pia mcp` serves one persistent, verified REPL session over MCP (stdio). It has exactly two tools. Everything else, such as listing definitions or showing proofs, is a REPL command that you send through `execute`. The rules of the session are the rules of `pia repl` (see the `pia-repl` skill and [docs/repl.md](../../docs/repl.md)).

## Setup

Build the binary and register it. The server's working directory is where `:load` resolves relative paths, so start it from the repository root:

```sh
bazel build //tools/pia
claude mcp add pia -- "$PWD/bazel-bin/tools/pia/pia" mcp
```

`pia mcp` takes `--no-run` (prove, never compile or run), `--allow-unproved=<spec>`, `--timeout-ms=N` (the solver's limit per obligation) and `--meta-cycles=N`. It takes no files and no `--json`: load files with `:load` instead.

## The two tools

| Tool | Arguments | Returns |
| --- | --- | --- |
| `execute` | `code` (required), `wait_ms` (default 10000), `json` (default false) | the cell's result as the text `pia repl` prints, or a job number if the cell is still running after `wait_ms` |
| `poll` | `job` (required), `wait_ms` (default 10000), `json` | the job's state, `queued`, `running` or `done`, and its result once done |

- **One `execute` is one cell.** `code` can hold several top-level items and several lines (`\n` in the JSON string). Commands start with `:`, such as `:env` or `:redef let ...`.
- **`isError` means the cell failed.** A failed proof, a type error or a refused `:redef` comes back with `isError: true` and the counterexamples in the text. Treat it as a result to act on, not as a tool failure. Nothing in a failed cell was committed, so retry with the fix.
- **A slow cell returns a job.** The text is `job N is running; call poll with this job number`. Call `poll {"job": N}` until the state is `done`. Jobs run one at a time, in order, so a slow cell holds up every later `execute`. For a long-running expression use `:spawn` (below) instead.
- **Leave `json` off.** Some clients, Claude Code among them, show you the structured content in place of the text, and the JSON events are several times longer. Turn it on only when you need machine-readable fields, such as a counterexample as an object.

## The built-in guide

The server teaches the language too. Its instructions are a short primer, `:help <topic>` returns one section of the `pia-language`, `pia-contracts` or this skill (`:help` lists the topics, and `pia://guide/<topic>` serves them as resources), and a failed cell ends with `hint:` lines that name the topic with the fix. If you have these skills loaded, you already have the guide; read a hint's topic when you do not.

## Reading a result

```text
bump : (a : u8) -> u8  (* 2 proved *)
```

A definition joined the environment, with its type and the number of obligations proved.

```text
[1]:1:28: failed: '+' does not overflow u8
  counterexample: a = 255, result = 256
[1]: error: 1 obligation failed; nothing was committed
```

`[cell]:line:col` locates the failed obligation, counting lines within that cell. The counterexample is one input that breaks it: the parameters (`len xs` for a slice length, `p.r` for a record field) plus `result`, `index` and `length`, or `amount` where they apply. The location can be in an *earlier* cell: when a `:redef` breaks a caller, the failure points into the caller's cell.

```text
- : u16 = 82
```

An expression's value. Expressions are proved, then compiled and run. They never join the environment.

## The working loop

1. **Send the smallest piece that can be proved alone**, usually one function. Callers come later, since they are proved against the callee's contract, not its body.
2. **Read every failure before changing anything.** Decide for each one whether it is a missing assumption (add `requires`), a real bug (change the body), or a mistake in your port (fix the port). The `pia-proof-debugging` skill covers this in detail.
3. **Resend with one change.** A name that is already defined cannot be defined again (Pia has no shadowing), so either resend after a failure (a failed cell defined nothing), or use `:redef let ...` to replace a definition that was committed.
4. **Use `:redef` to ask "who relies on this?".** It proves every definition that uses the replaced one again. If one breaks, the redefinition is refused and the error points at the caller.
5. **Run expressions to check behaviour**, once the definitions prove: `execute {"code": "bump 41"}`.
6. **Check the end state** with `:env`, and `:proof name` for how each obligation was settled.

## Commands you will use

| Send | To |
| --- | --- |
| `:env` | list the definitions and the cells they came from |
| `:type <expr>` | get a type without running anything |
| `:proof [<name>]` | list a definition's obligations and methods, or a summary |
| `:source <name>` | see the source of a committed definition |
| `:redef <code>` | replace definitions; dependents are proved again |
| `:forget <name>` | remove a definition nothing uses |
| `:allow [<spec>]` | accept unproved (not failed) obligations, by function or `[cell]:line[:col]` |
| `:load <file>` | run a `.pia` file, or the `pia` blocks of a `.pia.md`, as one cell |
| `:reset` | empty the environment, for example before loading a file that reuses names |
| `:spawn <expr>`, `:tasks`, `:wait <n>` | run an expression as a background task, list tasks, wait for one |

## Long-running work

`:spawn <expr>` proves the expression, starts it on its own thread and returns at once (`task 1 (...) running`). The session stays usable. `:wait 1` blocks until it finishes (it is itself a cell, so it may come back as a job to `poll`). While a task runs, `:redef` of a function it uses is swapped into it only when the new body is proved against the old contract; otherwise it waits up to two seconds for a moment when no task is inside the affected functions, and is refused if there is none. See the `pia-repl` skill.

## Pitfalls

- **Paths in `:load` are relative to the server's working directory**, not to your shell's.
- **No shadowing, anywhere.** `let x` inside a function cannot reuse a parameter's name. The error suggests a primed name such as `x'`.
- **Core builtins are taken.** `add`, `sub`, `mul` and similar names are builtins, so pick other names for your functions.
- **Calls inside contracts are unknown values.** `requires a < limit`, where `limit` is a constant definition, does not let the solver use `limit`'s value. Write the literal, or a spec function with an `ensures`.
- **Arrays and slices cannot be returned yet**, so they cannot be shown as values. Return a scalar or a record.
- **A transcript is not a test.** When a session matters, replay it as a `pia repl` file (see `pia-repl`), so the result can be checked.

## A replayable example

These cells are what an agent would send one `execute` at a time. Replayed through `pia repl`, which prints the same text as the server:

<!-- repl: mcp_loop.pia -->
```ocaml
let bump (a : u8) : u8 = a + 1
let bump (a : u8) : u8 requires a < 200 ensures result = a + 1 = a + 1
let double (a : u8) : u16 requires a < 100 ensures result = a + a = bump a + a - 1
double 41
:redef let bump (a : u8) : u8 requires a < 10 ensures result = a + 1 = a + 1
:redef let bump (a : u8) : u8 requires a < 255 ensures result = a + 1 = a + 1
:env
```

```console
$ pia repl < mcp_loop.pia
[1]:1:28: failed: '+' does not overflow u8
  counterexample: a = 255, result = 256
[1]: error: 1 obligation failed; nothing was committed
bump : (a : u8) -> u8  (* 2 proved *)
double : (a : u8) -> u16  (* 4 proved *)
- : u16 = 82
[3]:1:69: failed: the precondition of 'bump' holds
  counterexample: a = 64
[5]: error: 1 obligation failed; the redefinition is not committed
bump : (a : u8) -> u8  (redefined)  (* 2 proved *)
[3] let double : (a : u8) -> u16
[6] let bump : (a : u8) -> u8
```

Cell 1 fails, so cell 2 can define `bump` without `:redef`. Cell 5 would break `double` (cell 3 calls `bump` with `a < 100`), so the failure points into cell 3 and nothing changes. Cell 6 loosens the precondition instead, and `double` is proved again.
