# 17. Build with Bazel; depend on LLVM/MLIR and Z3 as Bazel modules

Date: 2026-11-20

Status: Accepted

## Context

The project needs reproducible builds of a C++ compiler against LLVM/MLIR and Z3, without vendoring a checkout of llvm-project. The Bazel Central Registry's `llvm-project` module stops at 17.0.4, which predates MLIR's `smt` dialect (LLVM 21.1).

## Decision

Use Bazel with bzlmod. Depend on llvm-project through its own bzlmod overlay module (`utils/bazel/MODULE.bazel` on llvm-project main) with a `git_override` pinned to a specific main commit, and on Z3 from the Bazel Central Registry. Do not vendor or check out llvm-project into the repository.

### Amendment, 2026-11-20: how the overlay is consumed

llvm-project's `utils/bazel/MODULE.bazel` (module `llvm-project-overlay`) only defines its source repository `@llvm-raw` when it is the root module, and the `@llvm-project` repository it configures is private to that module. A `bazel_dep` on it with a `git_override` therefore cannot give Pia's targets `@llvm-project//mlir:...`. Instead, `MODULE.bazel` does what the overlay's README recommends for downstream projects:

- fetch llvm-project as the module `@llvm-raw` with `bazel_dep` plus `git_override`, pinned to one main commit (`LLVM_COMMIT`). `patch_cmds` add a minimal root `MODULE.bazel` and the empty root files LLVM's `configure.bzl` expects. It has to be a module, because `MODULE.bazel` can only load `.bzl` files from modules, not from a repository made with `use_repo_rule`.
- run LLVM's own `llvm_configure` rule from it, for the AArch64 and X86 targets
- `bazel_dep` on the same modules as the overlay's `MODULE.bazel`, with the same repo names

Z3 builds through rules_foreign_cc's CMake rule. A one-line patch (`third_party/rules_foreign_cc/absolute_linker_path.patch`, applied with `single_version_override`) makes the linker path absolute so CMake can find Apple's wrapped clang.

This is still LLVM's own Bazel build at a pinned main commit, fetched by Bazel and never checked into the repository.

## Consequences

- Bumping LLVM means changing `LLVM_COMMIT`, re-syncing the mirrored `bazel_dep` list with the overlay's `MODULE.bazel` at that commit, and fixing any API breakage.
- First builds of LLVM/MLIR are long; remote or disk caching will matter.
