# Pia: Proved In Advance

**Pia is a programming language whose compiler proves your code correct before it runs.**

Every integer overflow, every array index and every contract in a Pia program is a proof obligation. The compiler discharges them at compile time, with interval analysis and the [Z3](https://github.com/Z3Prover/z3) SMT solver. When a proof fails, you get a compile error with a counterexample. When every proof succeeds, the checks are gone from the machine code, because they can never fail.

The quickest way to see it is the REPL, where every cell is proved before it runs, and the MCP server, which gives the same session to an agent such as Claude.

## Prove as you type: the REPL

`pia repl` is a verified REPL. Each definition joins a persistent environment only when everything in the environment still proves, and each expression is proved, then compiled and run. Here is a short session, one cell per line:

<!-- repl: home.pia -->
```ocaml
let bump (a : u8) : u8 = a + 1
let bump (a : u8) : u8 requires a < 255 = a + 1
bump 41
bump 255
let twice (a : u8) : u8 requires a < 100 = bump (bump a)
:redef let bump (a : u8) : u8 requires a < 10 = a + 1
twice 41
```

```console
$ pia repl < home.pia
REPL_OUTPUT
```

The first `bump` can overflow, so it is refused with the input that breaks it, and nothing is committed. The second adds a precondition and proves. `bump 255` breaks that precondition, so it is refused at compile time and never runs. `twice` is proved against `bump`, so the `:redef` that would tighten `bump` to `a < 10` is refused, with the error pointing at the call in `twice` that it would break. The environment is always a program that proves.

[The REPL](repl.md) page has the rest: state with invariants and verified migration, `:load` for files, and live redefinition of code that background tasks are running.

## A REPL for agents: the MCP server

`pia mcp` serves a REPL session over the [Model Context Protocol](https://modelcontextprotocol.io), so an agent can write Pia one proved cell at a time. It has two tools, `execute` and `poll`, and it teaches the language as it goes:

- **A primer when the agent connects**, under 2 KB: the binding form, bounded integers, where contracts go, no shadowing, and a list of guide topics.
- **`:help <topic>`** returns one section of the guide, such as `syntax`, `facts`, `contracts`, `loops` or `pitfalls`, cut from the same [agent skills](agents.md) the documentation tests prove.
- **A hint on every failed cell**, saying which kind of fix it needs and where to read about it.
- **What each proof cost**: the time for the cell, how many goals it raised and how each was proved, and the slowest solver goals with their Z3 resource counts.

Here is what Claude sees when it sends the first `bump` above, verbatim:

```text
>>> execute {"code": "let bump (a : u8) : u8 = a + 1"}
<<< (isError) [1]:1:28: failed: '+' does not overflow u8
  counterexample: a = 255, result = 256
[1]: error: 1 obligation failed; nothing was committed
hint: arithmetic is checked at the operands' width: bound the inputs with a range type (int{0..99}) or a requires, or widen with a typed let. (:help facts)
took 831 ms: verifying 205 ms (preparing 3.4 ms, solving 202 ms), parsing and compiling 626 ms
goals: 1 from this cell (0 by intervals, 1 by the solver) and 0 re-proved from the environment: 0 proved, 1 failed
slowest solver goals in this cell:
  202 ms  [1]:1:28 bump: '+' does not overflow u8 (failed, cost 357)
```

To use it from Claude Code, after [building Pia](getting-started.md):

```sh
claude mcp add pia -- "$PWD/bazel-bin/tools/pia/pia" mcp
```

[Agent skills](agents.md) teach an agent the working loop, and [Debugging C++ with the REPL](repl-debugging.md) follows Claude through a whole session, from a literal port of a C++ parser to a verdict and a fix.

## A first proof

<!-- example: average.pia -->
<!-- expect: fail -->
```ocaml
let average (a : u8) (b : u8) : u8
  ensures 2 * result <= a + b && a + b <= 2 * result + 1
= (a + b) / 2
```

This is the classic way to average two bytes, and it is wrong for large inputs, because `a + b` overflows a byte. Pia refuses it, and says why:

```console
$ piac --verify average.pia
average.pia:3:6: failed: '+' does not overflow u8
  counterexample: a = 255, b = 255, result = 510
average.pia:3:11: proved: the divisor is not zero [intervals]
average.pia:3:11: proved: '/' does not overflow u8 [intervals]
average.pia:2:3: proved: the postcondition holds [smt]
3 proved, 1 failed, 0 skipped
```

Add in a wider type, and every goal is proved, including the postcondition:

<!-- example: average_fixed.pia -->
```ocaml
let average (a : u8) (b : u8) : u8
  ensures 2 * result <= a + b && a + b <= 2 * result + 1
= let total : u16 = a + b in total / 2
```

```console
$ piac --verify average_fixed.pia
average_fixed.pia:3:23: proved: '+' does not overflow u16 [intervals]
average_fixed.pia:3:36: proved: the divisor is not zero [intervals]
average_fixed.pia:3:36: proved: '/' does not overflow u16 [intervals]
average_fixed.pia:3:3: proved: the value fits in u8 [smt]
average_fixed.pia:2:3: proved: the postcondition holds [smt]
5 proved, 0 failed, 0 skipped
```

## What is in Pia

- **A verified REPL and an MCP server.** `pia repl` proves every cell before it runs and checks every redefinition against the code that uses it; `pia mcp` gives that session to an agent, with a guide to the language, hints and proof costs.
- **Proved, not checked.** Overflow, bounds, division by zero, preconditions, postconditions, assertions and quantified properties are all proved at compile time. The strongest guarantee is the default, and weaker behaviour, such as wrapping arithmetic, is explicit.
- **An ML-style language.** One `let` for every definition, including types, which are values. Records as values, range types such as `int{0..255}`, and parameters that state their ownership and access.
- **Metaprogramming from day one.** Operators are metaprograms in the prelude, and derives such as `@derive(eq)` generate code that is then proved like code you wrote.
- **Built on MLIR.** `piac` proves goals in its own MLIR dialects, then compiles through LLVM to arm64 for Apple Silicon, with NEON vectorisation.
- **Proofs in your editor.** A language server shows failed goals and their counterexamples as you work, in VS Code or any LSP editor.

## Where to go next

- [Getting started](getting-started.md): build `piac`, prove a program, set up VS Code
- [The REPL](repl.md) and [agent skills](agents.md): prove cell by cell, by hand or with an agent over MCP
- [Pia and other verified languages](comparison.md): how Pia compares with Dafny, F\*, Lean, SPARK, Verus and others
- [Demo: edge detection](demo.md): a real program built with Pia, and a bug the compiler catches
- [Demo: stream delineation](streams.pia.md): a literate Pia program that finds the streams and watersheds in a terrain, with every step proved
- [A tour of Pia](tour.md): the language as it is today, every example tested
- [How verification works](verification.md): goals, intervals, Z3 and counterexamples
- [Status and roadmap](status.md): what works, what does not yet, and what is next
- [Language design](design.md): the whole language as designed
- [Architecture Decision Records](adr/README.md): why Pia is the way it is

Pia is open source under the Apache License 2.0, at [github.com/deanberris/pia-lang](https://github.com/deanberris/pia-lang). If you would like to support the work, you can [sponsor it on GitHub](https://github.com/sponsors/deanberris).
