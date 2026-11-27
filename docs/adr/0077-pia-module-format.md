# 77. A module format Pia controls: canonical expanded Pia, not MLIR bytecode

Date: 2026-11-28

Status: Proposed

## Context

[ADR 0076](0076-transparent-exports.md) needs per-module artifacts that a later step reads back. The whole-program mode (section 6) links each module's verified program before optimising. Transparent exports ship bodies to importers, and [abi.md](../abi.md) already plans an optional proof bundle in `__PIA_PROOF,__bundle` as "`pia_contract` MLIR bytecode".

MLIR bytecode would be the easy choice, and Dean ruled it out (2026-11-28): "I'm not sure I want to be tied to an (unstable, not guaranteed) MLIR bytecode. Let's explore specifying one that we control." The concern is real:

- MLIR's bytecode format has a version number, and readers accept older versions, but only within an LLVM release's policy. The builtin dialect and the upstream dialects Pia lowers through (`arith`, `scf`, `memref`, `func`, `linalg`) promise no stability. An op's operands, attributes or properties change between LLVM revisions. Their C++ APIs move just as fast: `arith::ExtFOp`'s builder was deprecated under us, which broke main's `-Werror` build (#495).
- Pia pins one LLVM revision per piac build and bumps it often. An artifact written by one piac would then be readable only by a piac at the same LLVM revision. A shared library or a shipped `Pia.*` module would have to be rebuilt by every piac that reads it.
- A certificate or a hash over MLIR bytecode would change when LLVM changes the encoding, even though the Pia program has not changed. Then every LLVM bump would invalidate every certificate.

What Pia already controls is the language. A `.piai` interface is canonical Pia source text: the interface's tokens, with whitespace normalised, items one per line, and exported definitions after it (`canonical` and `canonicalItem` in `src/syntax/Interfaces.cpp`). The interface hash is the SHA-256 of that text. ADR 0073 already versions the language and ships migration rules for every breaking change, so a format at that level has a stability story already.

## Options

| | A. Canonical expanded Pia | B. Pia's own encoding of the IR | C. MLIR bytecode |
| --- | --- | --- | --- |
| What it holds | The module after metaprogram expansion and sema, as canonical Pia text with names resolved and types written out | The `pia`, `pia_contract` and `pia_par` ops, with a fixed set of upstream ops, in a binary schema we define | MLIR's own encoding |
| Stable across LLVM bumps | Yes: it is the language | Only as long as we keep the upstream ops' meaning in step with LLVM's | No |
| Versioned by | ADR 0073's language and ABI version and migrations | A schema version of our own | MLIR's bytecode version |
| Reading it back | Parse, then sema and IRGen again (deterministic, no solving) | Decode straight into MLIR | Decode |
| Hash and certificate | Hash the text, as the interface hash already does | Hash the encoding | Changes with LLVM |
| Human-readable, diffable | Yes | No, a printer is needed | No |
| Cost | Re-runs sema and IRGen at the reader, a small share of a build (the solver is most of it) | A second serialiser to keep in step with the dialects | None to write |

## Decision (proposed): A, with a proof table beside it

A Pia module artifact, `.piam`, is the module as it is after metaprograms are expanded and sema has run, written as canonical Pia text:

- Every name is fully qualified, so the text depends on no import order or ADL.
- Every deduced type and generic argument is written out, so reading it back needs no inference.
- Every metaprogram call is replaced by its expansion, so no metaprogram runs again. Hygiene renames stay as they were, since `--dump-expanded` already prints them.
- `@lower` text stays as the source wrote it. It is MLIR, but it is the program's own trusted text, and the certificate already records its hash (ADR 0065).

Beside the text sits a **proof table**: for each obligation, its stable id (function, then the goal's index in walk order), its status and method, and the SHA-256 of its query. This is what codegen needs from a proof without solving it again: which arithmetic was proved to fit, and which accesses are in bounds. A reader regenerates the IR, walks the same goals, and takes each one's status from the table. A goal missing from the table, or one whose query hash differs, is an error, never a silent re-proof. The table replaces the "MLIR bytecode" in abi.md's proof bundle.

Integrity:

- The **module hash** is the SHA-256 of the canonical text. The certificate records it next to the interface hashes, so `pia-cert check` can tell that a `.piam` and an object came from the same program.
- The proof table is hashed into the certificate too. A tampered table fails the check just as a tampered certificate does.

Encoding: UTF-8 text, zstd-compressed when shipped in `__PIA_PROOF` or as a sidecar `.piam` file. The text form is the format itself, so there is no second format to keep in step with it.

## Consequences

- An LLVM bump changes no artifact, no hash and no certificate. Only a change to the language does, and ADR 0073's migration rules already cover those.
- A reader runs sema and IRGen again. Today those are a small share of a build next to Z3, and they are deterministic, so the IR the reader gets is the IR that was proved. The proof table's query hashes check this.
- Transparent bodies (ADR 0076, section 1) are the same canonical text as their module's `.piam`. So the inline surface in `.piai`, the whole-program mode's input and the proof bundle become one format at three scopes.
- LTO (ADR 0076, section 5) still uses LLVM bitcode. It is written and read by one toolchain within one build, so its instability does not matter, and it is never shipped as a stable artifact.
- What this gives up: reading a `.piam` costs a parse and an IRGen, and printing canonical expanded Pia needs a printer for every node kind. `--dump-expanded` is the start of one, but it prints a tree, not source.

## Steps

1. A canonical printer for the expanded tree, the inverse of the parser: `piac --emit=piam`. The test is that printing, parsing and printing again gives the same text, for every file in `tests/verify`.
2. The proof table, written with `--emit=piam` and read with `--verify --proof-table=<file>`, which takes statuses from it and fails on any mismatch.
3. Module hash and proof table hash in the certificate (format 4), with `pia-cert check` comparing them.
4. ADR 0076's whole-program mode and transparent bodies read `.piam`.
