# Contributing to Pia

Pia is built in the open, and contributions are welcome: bug reports, fixes, proofs, documentation, examples and new features. This file says how contributions are made and what is expected of the person who makes one.

## How a change lands

Every change reaches `main` through a pull request. A pull request is ready to merge when:

- `bazel build //...` and `bazel test //...` pass, which CI ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) checks for every pull request. That suite includes the proofs: Pia code in the repository must verify, and an unproved goal is a failure unless it is accepted narrowly and on purpose.
- Every example in the documentation still verifies and shows the real output of `piac` and `pia` (`bazel test //tests/docs:doc_examples_test` and `//tests/docs:skills_test`).
- A change to the documentation site still builds with `mkdocs build --strict`.
- A change to the language or the tools updates the [agent skills](skills/README.md) that teach it, which users install as a Claude Code plugin: `python3 tools/skills/check.py` fails when a new keyword or `piac` flag is in no skill.
- Changed C++ lines are formatted with `clang-format` (CI checks them), and the code follows the [style guide](docs/style.md): early returns rather than nested `if`s, comments that say why, and the LLVM Coding Standards.

A change to how the language works starts as a design note or an [Architecture Decision Record](docs/adr/README.md), so the reasoning is written down before the code.

## AI-assisted contributions

You may use AI tools to help with a contribution: coding agents such as Claude Code, chat assistants, code completion, or anything else. This applies to code, proofs, tests and documentation alike, and to a change written mostly by a tool as well as one where a tool helped a little.

Attribution is optional. You do not have to say that a tool was involved, and a commit or pull request does not need a `Co-Authored-By` trailer, a tool's signature or any other marker. You may add one if you like, and a contribution is treated the same either way.

The repository itself is set up for agents. The [Agent Skills](skills/README.md) in `skills/` teach a coding agent to use `piac`, `pia repl` and the `pia mcp` server, and Claude Code loads them automatically in a checkout.

## You own what you submit

Whoever opens a pull request is its author and is responsible for all of it, however it was written. In particular:

- **It must pass.** The proofs, the tests and the documentation checks above must pass. A tool's output gets no exemption, and "the model wrote it" does not explain a failure.
- **Understand it.** Be ready to explain any line of the change, answer questions about it in review, and fix it if it turns out to be wrong.
- **Do not weaken the guarantees to get green.** Do not skip, disable or loosen a test, accept an unproved goal or add `unsafe` just to make a change pass. If a goal really cannot be proved yet, say so in the pull request and accept it as narrowly as possible.
- **You have the right to submit it.** The contribution must be yours to license. Do not submit code a tool reproduced from a source whose licence does not allow it, and do not include secrets or credentials.

## Licence of contributions

Pia is licensed under the [Apache License 2.0](LICENSE). Under section 5 of that licence, anything you intentionally submit for inclusion is contributed under the same terms, with no additional conditions. That holds whether or not a tool helped you write it.

## Contributors

Pia was started by [Dean Michael Berris](https://github.com/deanberris). Everyone who has contributed is listed by Git, in `git shortlog -sn`, and on GitHub's [contributors page](https://github.com/deanberris/pia-lang/graphs/contributors).
