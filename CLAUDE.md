# Working in this repository

Pia is a language whose programs are proved before they compile: a C++ compiler on MLIR and Z3, built with Bazel.

**Navigate by the map, not by reading code.** [CODEMAP.md](CODEMAP.md) says where everything lives and which file to open for a task, with build and test commands. Before opening any file over about 1,500 lines (`IRGen.cpp`, `Verifier.cpp`, `Session.cpp`, `Parser.cpp`, `Codegen.cpp`), outline it and read only the lines you need:

```sh
python3 tools/codemap/outline.py --grep <word> src/irgen/IRGen.cpp
```

**Writing Pia?** Load the `pia-language` skill. For failed goals, use `pia-contracts`. To run the prover, use `piac-verify` and `pia-fast-proofs`, and to work cell by cell, `pia-repl` or `pia-mcp`. The skills are in `skills/`, linked from `.claude/skills`. For a working example of a feature, look in `tests/verify/<feature>.pia`.

**House rules:**

- Every change goes through a pull request. Design changes start as an ADR in `docs/adr/` (see `docs/adr/README.md`).
- C++ follows [docs/style.md](docs/style.md): the LLVM Coding Standards with MLIR naming, early returns, and comments that say why. CI runs `git clang-format` on the lines you changed.
- Every `ocaml` block in the tested docs and skills is proved, and every `$ piac` console block must match real output (`tests/docs`). Get that output from a real run, never by hand.
- If you add, move or delete a file, update its line in `CODEMAP.md` in the same PR. `python3 tools/codemap/check.py` says what is missing.
- Bazel builds LLVM, MLIR and Z3 from source, so a cold build takes a long time. Prefer a narrow target (`bazel test //tests/verify:loops_test`). `src/syntax`, `src/meta` and `src/lsp` also compile with plain `g++ -std=c++17 -Isrc` for quick checks.
- Clean up after yourself: remove temporary files and finished worktrees, and `bazel clean` worktrees you no longer need.
