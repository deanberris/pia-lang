# Agent skills for Pia

These are [Agent Skills](https://agentskills.io): folders with a `SKILL.md` that teach a coding agent, such as Claude Code, to write Pia and use its tools well. Each `SKILL.md` starts with a `name` and a `description` that tell the agent when to load it, and every command and example in them is checked by `//tests/docs:skills_test` against the real `piac` and `pia`.

| Skill | Teaches |
| --- | --- |
| [pia-language](pia-language/SKILL.md) | writing idiomatic Pia: syntax at a glance, where each fact belongs, the usual shapes for loops, errors, generics, lambdas and modules, and the pitfalls |
| [pia-porting](pia-porting/SKILL.md) | porting from C, C++, Rust, OCaml, Zig and Go: a feature map, what is not built yet, and each language's traps |
| [pia-idioms](pia-idioms/SKILL.md) | acting on each lint, when to keep a form with `@allow`, and keeping proofs cheap |
| [pia-contracts](pia-contracts/SKILL.md) | writing `requires`, `ensures`, loop invariants and `decreases`, and fixing each kind of failed goal |
| [piac-verify](piac-verify/SKILL.md) | `piac --verify`: the goal report, counterexamples, `--allow-unproved`, solver limits, other modes |
| [piac-build](piac-build/SKILL.md) | compiling and linking: emit modes, targets, modules and interfaces, C interop, the Bazel rules, trust reports and proof certificates |
| [pia-lean](pia-lean/SKILL.md) | proving a lemma in Lean 4 when Z3 cannot: `= by lean T`, `--emit=lean`, the proof file, `pia_lean_proof` receipts and stale receipts |
| [pia-fast-proofs](pia-fast-proofs/SKILL.md) | proving only what changed: `--verify-only`, `--proof-cache`, `--jobs`, `--verify-stats`, slicing |
| [pia-mcp](pia-mcp/SKILL.md) | driving a verified session through the `pia mcp` server's `execute` and `poll` tools |
| [pia-repl](pia-repl/SKILL.md) | `pia repl` from a shell: piped cells, JSON lines, `:redef`, state with invariants and `old`, tasks |
| [pia-proof-debugging](pia-proof-debugging/SKILL.md) | deciding whether C, C++ or Rust code is correct by porting it into REPL cells and working through counterexamples |

## Installing

The pack is also a Claude Code plugin, with the `pia-lsp` language server and the `pia mcp` server alongside the skills ([`.claude-plugin/`](../.claude-plugin)). [docs/agents.md](../docs/agents.md) has the install steps for Claude Code and other agents; in short:

```sh
claude plugin marketplace add deanberris/pia-lang
claude plugin install pia@pia-lang
```

In a checkout of this repository, Claude Code finds the skills by itself through `.claude/skills`.

## Changing a skill

Keep each skill short and about one job. A Pia example in a ` ```ocaml ` block must verify unless it is marked, and a ` ```console ` block that starts with `$ piac` or `$ pia` must show the command's real output; the markers are described in `tests/docs/doc_examples_test.py`. Run the checks with:

```sh
python3 tools/skills/check.py          # the pack is complete: wiring, manifests, keywords, piac flags
python3 tools/docs/check.py            # the public docs keep up: keywords, flags, attributes, feature tests, modules
bazel test //tests/docs:skills_test    # every example proves and every command prints what it shows
```

**Feature changes update the pack.** A pull request that adds or changes a language feature, a keyword, a `piac` flag or a lint updates the skill that teaches it in the same pull request: the syntax table in `pia-language`, the feature map in `pia-porting` (moving the feature out of "Designed, not built yet" when it lands), `pia-idioms` for a lint, `piac-build` or `piac-verify` for a flag. `tools/skills/check.py` fails when a keyword or flag is in no skill. A new skill also needs a line in `tests/docs/BUILD.bazel`, the tables here and in `docs/agents.md`, a `.claude/skills` link and a `CODEMAP.md` line, which the check lists. The same pull request updates the public docs too (`docs/features.md`, `docs/library.md`, the page that teaches the feature, and `docs/status.md`); `tools/docs/check.py` fails until it does. A new `##` section in `pia-language`, `pia-contracts` or `pia-mcp` is also a `pia mcp` help topic: map it in `src/repl/embed_guide.py`.
