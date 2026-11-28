# 85. Release 1.0: a Pia front end in Pia over Pia IR, and its gates

Date: 2026-11-28

Status: Proposed

## Context

The [roadmap](../roadmap.md) (Dean, 2026-11-27, agreed 2026-11-28) makes 1.0 the release where Pia's front end is written in Pia, works over Pia IR ([ADR 0079](0079-pia-module-format.md)), and still lowers to MLIR and LLVM, so Pia keeps the open-source state of the art as it moves.

Dean's decisions that shape it (2026-11-27):

- **Which passes move, in order**: every front-end pass (lexing, parsing, metaprogram expansion, sema, IRGen to Pia IR, verification) and SAT-based pruning with the 0.5.0 solver move into Pia; everything else lowers to MLIR as it does today; then the analyses and optimisations unique to Pia are lifted to Pia IR as passes written in Pia.
- **The C++ piac stays as the bootstrap compiler until Pia 3.0**, when a binary of the Pia 2.0 compiler builds 3.0 on its own. It is retired then, and git history keeps every compiler so the chain can be re-bootstrapped from source.

## Decision

The release policy of [ADR 0080](0080-release-0-1-0-gates.md) applies.

### Libraries, which gate the 1.0 tag

1. **Pia IR in Pia**: `Pia.Ir`, an encoder and decoder proved to round-trip against `docs/ir.md`, with the schema in `lib/Pia/Ir/Schema.pia` (ADR 0079 step 7).
2. **The front end in Pia**: lexer, parser, metaprogram expansion, sema and IRGen, producing Pia IR. The parser is proved against the grammar and expansion against its fixed-point rule.
3. **Verification in Pia**: the obligation walk over Pia IR, solved by the 0.5.0 solver and Z3, with Lean for what they cannot prove.
4. **SAT-based pruning** in Pia IR before lowering: branches, cases and checks the prover shows unreachable or redundant are removed.
5. **Lowering to MLIR and LLVM** through 0.4.0's C++ FFI, using the schema's generated mapping, so an LLVM bump changes the mapping and nothing else.
6. **Pia bindings for MLIR and LLVM**, published as a library and offered upstream.
7. **Stability**: from 1.0, the language, the standard library's interfaces, Pia IR and the certificate format change only through ADR 0073 and ADR 0079 migrations, with one release of deprecation.

### The demo and exit criteria, which close the 1.0 series

- The Pia front end compiles the standard library and the 0.1.0 to 0.5.0 demos, and its output matches the C++ piac's on the round-trip suite: the same proof reports and the same Pia IR.
- **A bootstrap**: the C++ piac builds the Pia front end, which builds itself, and the second and third builds are byte-identical in Pia IR. CI runs the bootstrap on every release.
- The Pia-specific passes (using proved facts to optimise, record and layout transforms, ADR 0076's cross-module unfolding) start moving to Pia IR; the first ones moved are listed, the rest follow in 1.x.

## Consequences

- Two front ends exist until Pia 3.0, and CI checks that they agree.
- Every LLVM or MLIR bump after 1.0 touches only the generated mapping and the bindings.
- 1.0's stability promise starts the migration rules in earnest for everyone using Pia.
