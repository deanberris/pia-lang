# 17. Build with Bazel; depend on LLVM/MLIR and Z3 as Bazel modules

Date: 2026-11-20

Status: Accepted

## Context

The project needs reproducible builds of a C++ compiler against LLVM/MLIR and Z3, without vendoring a checkout of llvm-project. The Bazel Central Registry's `llvm-project` module stops at 17.0.4, which predates MLIR's `smt` dialect (LLVM 21.1).

## Decision

Use Bazel with bzlmod. Depend on llvm-project through its own bzlmod overlay module (`utils/bazel/MODULE.bazel` on llvm-project main) with a `git_override` pinned to a specific main commit, and on Z3 from the Bazel Central Registry. Do not vendor or check out llvm-project into the repository.

## Consequences

- Bumping LLVM means changing one pinned commit and fixing any API breakage.
- First builds of LLVM/MLIR are long; remote or disk caching will matter.
