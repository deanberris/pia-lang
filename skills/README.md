# Agent skills for Pia

These are [Agent Skills](https://agentskills.io): folders with a `SKILL.md` that teach a coding agent, such as Claude Code, to use Pia's tools well. Each `SKILL.md` starts with a `name` and a `description` that tell the agent when to load it, and every command and example in them is checked by `//tests/docs:skills_test` against the real `piac` and `pia`.

| Skill | Teaches |
| --- | --- |
| [pia-mcp](pia-mcp/SKILL.md) | driving a verified session through the `pia mcp` server's `execute` and `poll` tools |
| [pia-repl](pia-repl/SKILL.md) | `pia repl` from a shell: piped cells, JSON lines, `:redef`, state with invariants and `old`, tasks |
| [piac-verify](piac-verify/SKILL.md) | `piac --verify`: the goal report, counterexamples, `--allow-unproved`, solver limits, other modes |
| [pia-fast-proofs](pia-fast-proofs/SKILL.md) | proving only what changed: `--verify-only`, `--proof-cache`, `--jobs`, `--verify-stats`, slicing |
| [pia-contracts](pia-contracts/SKILL.md) | writing `requires`, `ensures`, loop invariants and `decreases`, and fixing each kind of failed goal |
| [pia-proof-debugging](pia-proof-debugging/SKILL.md) | deciding whether C or C++ code is correct by porting it into REPL cells and working through counterexamples |

## Installing

Claude Code finds them automatically in this repository, through `.claude/skills`. To use them elsewhere, copy or link the folders into `~/.claude/skills/` (every project) or another project's `.claude/skills/`:

```sh
ln -s "$PWD"/skills/pia* ~/.claude/skills/
```

Other agents that read Agent Skills take the same folders; see the agent's documentation for where it looks. An agent without skill support can be pointed at a `SKILL.md` directly, as instructions.

The MCP server needs a build of `pia`:

```sh
bazel build //tools/pia //tools/piac
claude mcp add pia -- "$PWD/bazel-bin/tools/pia/pia" mcp
```

## Changing a skill

Keep each skill short and about one job. A Pia example in a ` ```ocaml ` block must verify unless it is marked, and a ` ```console ` block that starts with `$ piac` or `$ pia` must show the command's real output; the markers are described in `tests/docs/doc_examples_test.py`. Run the check with:

```sh
bazel test //tests/docs:skills_test
```
