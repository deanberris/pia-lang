# Agent skills

Pia ships a pack of [Agent Skills](https://agentskills.io) for coding agents such as Claude Code. A skill is a folder with a `SKILL.md`: instructions the agent loads when its description matches the task. These teach an agent to use Pia's tools the way they are meant to be used: prove one piece at a time, read counterexamples for what they say, state assumptions as contracts, and keep proof time down.

They live in [`skills/`](https://github.com/deanberris/pia-lang/tree/main/skills) in the repository. Every Pia example and every `piac` and `pia` command in them is run by the documentation tests (`//tests/docs:skills_test`), so they cannot drift from what the tools do.

| Skill | When an agent uses it |
| --- | --- |
| [`pia-mcp`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-mcp/SKILL.md) | a `pia mcp` server is connected: how `execute` and `poll` behave, reading results, the working loop, long-running cells |
| [`pia-repl`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-repl/SKILL.md) | no MCP connection: `pia repl` on a pipe or with JSON lines, `:redef`, state with invariants and `old`, tasks, saving a session as a test |
| [`piac-verify`](https://github.com/deanberris/pia-lang/blob/main/skills/piac-verify/SKILL.md) | proving or compiling files: the goal report, counterexamples, `--allow-unproved`, solver limits |
| [`pia-fast-proofs`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-fast-proofs/SKILL.md) | a proof is slow, or one function is changing in a big file: `--verify-only`, `--proof-cache`, `--jobs`, `--verify-stats`, slicing |
| [`pia-contracts`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-contracts/SKILL.md) | writing or repairing contracts: which fix each kind of failed goal needs, loop invariants, `decreases`, spec functions |
| [`pia-proof-debugging`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-proof-debugging/SKILL.md) | "is this C++ correct?": port it into cells, classify each counterexample, check assumptions against callers, report a verdict |

## Installing them

In a checkout of the repository, Claude Code finds the skills by itself, through `.claude/skills`. To use them in other projects, link them into your own skills folder:

```sh
ln -s "$PWD"/skills/pia* ~/.claude/skills/
```

Other agents that support Agent Skills read the same folders. An agent without skill support can be given a `SKILL.md` as plain instructions.

The `pia-mcp` skill needs the [MCP server](repl.md#mcp-server):

```sh
bazel build //tools/pia //tools/piac
claude mcp add pia -- "$PWD/bazel-bin/tools/pia/pia" mcp
```

## What a session looks like

[The REPL](repl.md#claude-driving-a-session) page shows Claude driving a session over MCP, and [Debugging C++ with the REPL](repl-debugging.md) follows the proof-debugging loop from a literal port of a parser to a verdict and a fix.

## Contributing with an agent

Contributions written with an agent are welcome, and they need no `Co-Authored-By` trailer or other attribution. The person who opens the pull request owns it, and it must pass the proofs and tests like any other change. [CONTRIBUTORS.md](https://github.com/deanberris/pia-lang/blob/main/CONTRIBUTORS.md) has the policy.
