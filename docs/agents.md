# Agent skills

Pia ships a pack of [Agent Skills](https://agentskills.io) for coding agents such as Claude Code. A skill is a folder with a `SKILL.md`: instructions the agent loads when its description matches the task. These teach an agent to use Pia's tools the way they are meant to be used: prove one piece at a time, read counterexamples for what they say, state assumptions as contracts, and keep proof time down.

They live in [`skills/`](https://github.com/deanberris/pia-lang/tree/main/skills) in the repository. Every Pia example and every `piac` and `pia` command in them is run by the documentation tests (`//tests/docs:skills_test`), so they cannot drift from what the tools do.

| Skill | When an agent uses it |
| --- | --- |
| [`pia-language`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-language/SKILL.md) | writing or reviewing Pia code: syntax at a glance, where each fact belongs (types before contracts), the usual shapes for loops, errors, generics, lambdas and modules, and the pitfalls |
| [`pia-porting`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-porting/SKILL.md) | porting from C, C++, Rust, OCaml, Zig or Go: a feature map from each language to Pia, what is designed but not built yet, and the traps each language sets |
| [`pia-idioms`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-idioms/SKILL.md) | a lint fired, or code is being reviewed for idiom: the rewrite each lint wants, when to keep a form with `@allow`, and keeping proofs cheap |
| [`pia-contracts`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-contracts/SKILL.md) | writing or repairing contracts: which fix each kind of failed goal needs, loop invariants, `decreases`, spec functions |
| [`piac-verify`](https://github.com/deanberris/pia-lang/blob/main/skills/piac-verify/SKILL.md) | proving files: the goal report, counterexamples, `--allow-unproved`, solver limits |
| [`piac-build`](https://github.com/deanberris/pia-lang/blob/main/skills/piac-build/SKILL.md) | compiling and linking: emit modes, targets, modules and interfaces, calling C, the Bazel rules, `--trust-report` and proof certificates with `pia-cert` |
| [`pia-fast-proofs`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-fast-proofs/SKILL.md) | a proof is slow, or one function is changing in a big file: `--verify-only`, `--proof-cache`, `--jobs`, `--verify-stats`, slicing |
| [`pia-mcp`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-mcp/SKILL.md) | a `pia mcp` server is connected: how `execute` and `poll` behave, reading results, the working loop, long-running cells |
| [`pia-repl`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-repl/SKILL.md) | no MCP connection: `pia repl` on a pipe or with JSON lines, `:redef`, state with invariants and `old`, tasks, saving a session as a test |
| [`pia-proof-debugging`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-proof-debugging/SKILL.md) | "is this C, C++ or Rust correct?": port it into cells, classify each counterexample, check assumptions against callers, report a verdict |
| [`pia-lean`](https://github.com/deanberris/pia-lang/blob/main/skills/pia-lean/SKILL.md) | proving a lemma in Lean 4 when Z3 cannot: `= by lean T`, `piac --emit=lean`, the proof file, `pia_lean_proof` receipts, stale receipts |


## Installing them

### Claude Code

The repository is a Claude Code plugin marketplace. Its one plugin, `pia`, installs the skills, the [`pia-lsp`](getting-started.md#vs-code) language server for `.pia` files, so Claude sees proof failures and lints as diagnostics as it edits, and the [`pia mcp`](repl.md#mcp-server) server, so it can prove and run code cell by cell:

```sh
claude plugin marketplace add deanberris/pia-lang
claude plugin install pia@pia-lang
```

or, inside Claude Code, `/plugin marketplace add deanberris/pia-lang` and then `/plugin install pia@pia-lang`. The plugin follows the repository's `main` branch, so `claude plugin marketplace update pia-lang` brings the skills up to date with the language. Plugin skills are namespaced, as in `/pia:pia-porting`, and Claude loads them by itself when a task matches.

The language server and the MCP server are the repository's own tools, so they must be on your `PATH`. There are no release binaries before 0.1; build them and link them (a link into `bazel-bin` stays current after each rebuild):

```sh
bazel build //tools/pia //tools/pia-lsp //tools/piac
mkdir -p ~/.local/bin
ln -sf "$PWD"/bazel-bin/tools/pia/pia "$PWD"/bazel-bin/tools/pia-lsp/pia-lsp \
       "$PWD"/bazel-bin/tools/piac/piac ~/.local/bin/
```

Without them the skills still load, and `/mcp` shows the `pia` server as failed to connect until `pia` is found. In a checkout of the repository, Claude Code also finds the skills by itself, through `.claude/skills`.

### Other agents

Any agent that reads [Agent Skills](https://agentskills.io) takes the same folders: copy or link `skills/pia*` into the directory the agent reads skills from (for Claude Code without the plugin, `~/.claude/skills/`):

```sh
ln -s "$PWD"/skills/pia* ~/.claude/skills/
```

An agent without skill support can be given a `SKILL.md` as plain instructions. Any MCP client can run the REPL server as `pia mcp` over stdio; its `initialize` instructions teach the basics of the language, and `:help <topic>` returns a section of these skills. Any LSP client can run `pia-lsp --stdio`; the [VS Code extension](getting-started.md#vs-code) does.

### Keeping them current

The skills are tested like the documentation. `//tests/docs:skills_test` proves every Pia example in them and runs every `piac` and `pia` command they show against the current compiler, and `tools/skills/check.py`, which CI runs on every pull request, fails when a keyword the lexer knows or a flag `piac` accepts is in no skill, or when a skill is missing from the plugin, the tests or these tables. `tools/docs/check.py` does the same for these pages: a feature, flag or library module that no public page mentions fails it. A pull request that adds a feature updates the skill that teaches it, and the documentation ([CONTRIBUTORS.md](https://github.com/deanberris/pia-lang/blob/main/CONTRIBUTORS.md)).

## What a session looks like

[The REPL](repl.md#claude-driving-a-session) page shows Claude driving a session over MCP, and [Debugging C++ with the REPL](repl-debugging.md) follows the proof-debugging loop from a literal port of a parser to a verdict and a fix.

## Contributing with an agent

An agent working on the compiler itself should start from [`CLAUDE.md`](https://github.com/deanberris/pia-lang/blob/main/CLAUDE.md), which Claude Code loads by itself, and [`CODEMAP.md`](https://github.com/deanberris/pia-lang/blob/main/CODEMAP.md), a map of where everything lives and which file to open for each kind of change. `python3 tools/codemap/outline.py <file>` lists a large file's functions with their line numbers, so an agent can read only the part it needs.

Contributions written with an agent are welcome, and they need no `Co-Authored-By` trailer or other attribution. The person who opens the pull request owns it, and it must pass the proofs and tests like any other change. [CONTRIBUTORS.md](https://github.com/deanberris/pia-lang/blob/main/CONTRIBUTORS.md) has the policy.
