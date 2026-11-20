# 11. Compiler in C++ on MLIR, verifying with interval analysis then Z3

Date: 2026-11-20

Status: Accepted

## Context

The prototype must reach Apple Silicon codegen and solver-backed verification quickly, reusing existing infrastructure.

## Decision

The compiler is C++ on MLIR. Pia lowers to its own dialects that carry contracts, then verification runs interval analysis first to discharge cheap obligations, and sends the rest to Z3. For the solver encoding, Pia targets MLIR's upstream `smt` dialect (from CIRCT, upstream since LLVM 21.1), exported to SMT-LIB and handed to Z3 in-process; a direct Z3 C++ API bridge is the fallback if the exporter is too limiting. Machine integers are bit-vectors, floats use the FP theory, and `dyn` tags are datatypes. Codegen goes through `linalg`/`vector` to `arm_neon` and LLVM for arm64.

## Consequences

- Requires an LLVM new enough to have the `smt` dialect (see ADR 0017).
- Pipeline order: parse, expand (fixed point), type check, lower, verify, optimise with proved facts, codegen.
