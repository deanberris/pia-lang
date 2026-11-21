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
| `:load <file>` | run a file as one cell |
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
| `defined`, `redefined` | `name`, `type`, `value` | a definition joined the environment; `value` for a constant; `type` is `type`, `meta` or `operator` for those items |
| `removed` | `name` | `:forget` removed it |
| `value` | `type`, `value` | an expression's value |
| `type` | `text`, `type` | `:type`'s answer |
| `proof` | `name`, `status`, `text`, `method`, `counterexample`, `where` | one obligation: `status` is `proved`, `failed`, `unproved` or `allowed`, `text` the claim, `counterexample` an object of names and values |
| `error` | `text`, `where` | |
| `info` | `text` | command output and notes |

`where` is `{"cell", "line", "column"}`. The exit status is 1 if any cell failed.

## MCP server

`pia mcp` serves a persistent REPL session over the Model Context Protocol (stdio transport), so an agent such as Claude can use Pia interactively. It has exactly two tools, in the style of Code Mode:

- **`execute {code, wait_ms?}`** runs a cell, code or a command, in the session. It waits up to `wait_ms` (10 seconds by default) and returns the cell's result: the rendered text, and the JSON result above as structured content. A cell that is still running returns its job number instead.
- **`poll {job, wait_ms?}`** waits for a job and returns its state (`queued`, `running` or `done`) and, once it is done, its result.

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
- Live redefinition of code that is still running, and metaprograms that read and rewrite the environment (`Pia.Live`), are designed in [ADR 0031](adr/0031-verified-repl-and-live-environment.md) but not built yet. Today each evaluation runs to completion before the next cell starts.
