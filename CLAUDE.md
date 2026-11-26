# Working in this repository

Pia is a language whose programs are proved before they compile: a C++ compiler on MLIR and Z3, built with Bazel.

**Navigate by the map, not by reading code.** [CODEMAP.md](CODEMAP.md) says where everything lives and which file to open for a task, with build and test commands. Before opening any file over about 1,500 lines (`IRGen.cpp`, `Verifier.cpp`, `Session.cpp`, `Parser.cpp`, `Codegen.cpp`), outline it and read only the lines you need:

```sh
python3 tools/codemap/outline.py --grep <word> src/irgen/IRGen.cpp
```

**Writing Pia?** Load the `pia-language` skill, and `pia-porting` when translating from another language. For lints, use `pia-idioms`; for failed goals, `pia-contracts`. To run the prover, use `piac-verify` and `pia-fast-proofs`; to compile and link, `piac-build`; and to work cell by cell, `pia-repl` or `pia-mcp`. The skills are in `skills/`, linked from `.claude/skills`. For a working example of a feature, look in `tests/verify/<feature>.pia`.

**House rules:**

- Every change goes through a pull request. Design changes start as an ADR in `docs/adr/` (see `docs/adr/README.md`).
- C++ follows [docs/style.md](docs/style.md): the LLVM Coding Standards with MLIR naming, early returns, and comments that say why. CI runs `git clang-format` on the lines you changed.
- Every `ocaml` block in the tested docs and skills is proved, and every `$ piac` console block must match real output (`tests/docs`). Get that output from a real run, never by hand.
- If you add, move or delete a file, update its line in `CODEMAP.md` in the same PR. `python3 tools/codemap/check.py` says what is missing.
- **A feature PR updates the skill pack** (`skills/`, installed by users as the `pia` Claude Code plugin). A new or changed keyword, syntax, flag, lint or built feature changes the skill that teaches it in the same PR: `pia-language`'s syntax table, `pia-porting`'s feature map (move it out of "Designed, not built yet" when it lands), `pia-idioms` for a lint, `piac-build` or `piac-verify` for a flag. `python3 tools/skills/check.py` fails when a keyword or piac flag is in no skill, and `bazel test //tests/docs:skills_test` proves the examples.
- Bazel builds LLVM, MLIR and Z3 from source, so a cold build takes a long time. Prefer a narrow target (`bazel test //tests/verify:loops_test`). `src/syntax`, `src/meta` and `src/lsp` also compile with plain `g++ -std=c++17 -Isrc` for quick checks.
- **CI is the build and the merge gate, not the iMac** (Dean, 2026-11-26). Push the branch and read its checks: `bazel test (Linux x86_64)` and `bazel test (macOS arm64)` (build and tests) must both be green, and so must the Linux proof-cost shards, which the `proof benchmark (Linux)` check stands for. No other benchmark gates: the nightly macOS shards and wall times are reports. A cached CI run takes about 10 minutes on Linux. Do not use the iMac for builds or tests; it runs only what needs its GPU, which is the demos. If you must use it for those, its build queue applies: `tools/imac/install.sh` caps each Bazel command at 6 jobs and queues plain `bazel` machine-wide (`bazelq --status`, `bazelq --exec -- <command>` for other heavy runs, `piac --jobs=6` at most), and never call `/opt/homebrew/bin/bazel` directly or set `BAZELQ_HELD`.
- Clean up after yourself: remove temporary files and finished worktrees, and `bazel clean` worktrees you no longer need.
