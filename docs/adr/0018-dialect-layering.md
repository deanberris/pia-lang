# 18. Three Pia dialects over upstream MLIR, with `smt` for solving

Date: 2026-11-20

Status: Accepted

## Context

The compiler needs IR for Pia's own types and values, for contracts that must be proved and then erased, and for concurrency. Upstream MLIR already provides codegen dialects and, since LLVM 21.1, an `smt` dialect with SMT-LIB export.

## Decision

Define three Pia dialects: `pia` (types, values, functions with parameter modifiers), `pia_contract` (contracts and proof obligations as ops), and `pia_par` (tiles, `spread` loops, collectives, placement). The verifier encodes obligations in the upstream `smt` dialect and hands SMT-LIB to Z3 in-process. After verification, contracts are erased, proved facts remain as attributes, and code lowers through upstream `arith`, `scf`, `memref`, `vector`, `linalg`, `arm_neon` and `llvm`. Interval analysis builds on MLIR's integer range analysis.

## Consequences

- One verifier pipeline handles both explicit contracts and implicit obligations.
- Pia avoids maintaining its own solver IR.
- GPU placement needs a path to Metal that upstream MLIR does not provide directly; this is deferred until the concurrency milestone.
