# 79. Pia IR: a versioned op schema Pia controls, in lock-step with piac, with deprecations and migrations

Date: 2026-11-28

Status: Proposed. Amended by [ADR 0080](0080-protocol-buffers-in-pia.md) (Proposed, 2026-11-28): the schema becomes `lib/Pia/Ir/ir.proto` and the encoding becomes protobuf's wire format in a canonical form, with strict must-understand fields; versions, migrations and the proof table stay.

## Context

[ADR 0076](0076-transparent-exports.md) needs per-module artifacts that a later step reads back. The whole-program mode (section 6) links each module's verified program before optimising. Transparent exports ship bodies to importers, and [abi.md](../abi.md) already plans an optional proof bundle in `__PIA_PROOF,__bundle` as "`pia_contract` MLIR bytecode".

MLIR bytecode would be the easy choice, and Dean ruled it out (2026-11-28): "I'm not sure I want to be tied to an (unstable, not guaranteed) MLIR bytecode. Let's explore specifying one that we control." The concern is real:

- MLIR's bytecode format has a version number, and readers accept older versions, but only within an LLVM release's policy. The builtin dialect and the upstream dialects Pia lowers through (`arith`, `scf`, `memref`, `func`, `math`, `linalg`, `tensor`) promise no stability: an op's operands, attributes or properties change between LLVM revisions. Their C++ APIs move just as fast. `arith::ExtFOp`'s builder was deprecated under us, which broke main's `-Werror` build (#495).
- Pia pins one LLVM revision per piac build and bumps it often. An artifact written by one piac would be readable only by a piac at the same LLVM revision.
- A certificate or hash over MLIR bytecode would change when LLVM changes the encoding, even though the program has not changed.

Dean then set the direction (2026-11-28): "We can write a versioned schema which can encode whatever MLIR op we support/use in the compiler and have that schema be enforced in lock-step with the compiler/language version. We have an opportunity here to define a deprecation path and a migration policy for the bytecode too like we're planning on doing with the source code." ADR 0073, section 5, is that policy for source. This ADR is the same policy for the IR.

## Decision

### 1. The schema: every op piac writes, named and numbered by Pia

**Pia IR** is defined by one checked-in schema, written in Pia: `lib/Pia/Ir/Schema.pia`, a table of records, one per op and one per type (section 7 says why it is Pia and not TableGen). It lists every op that can appear in a verified module, which is the input of codegen and of ADR 0076's whole-program mode:

- Pia's own dialects: `pia`, `pia_contract`, `pia_par`.
- Every upstream op piac emits or keeps: the `arith`, `scf`, `memref`, `func`, `math`, `linalg`, `tensor` and `async` ops that IRGen, the transforms and the `@lower` checks produce.

For each op, the schema gives:

- A **stable numeric id**, never reused.
- The **schema version** that introduced it, and the one that deprecated it, if any.
- Its **fields**: operands, results, regions and attributes, each with a Pia-defined type such as `u64`, `i1`, `string`, `type`, `value`, `region`, an enum by name or a list. Upstream properties are flattened into named fields.
- Its **meaning**: a line saying what it computes, written in the schema, not inherited from upstream documentation.

Types are in the schema too (`!pia.int<lo, hi>`, slices, records, sorts, and the upstream `i1`, `iN`, `index`, `f32`, `f64`, `memref` and `tensor` shapes), each with its own id.

So Pia IR is a description of the ops Pia uses, at the meaning Pia gives them. The **mapping** from each schema op to the current MLIR op is generated code in piac, `src/ir/Map.cpp`, produced from the schema by `tools/ir/gen`, which reads it through `piac --emit=interface`'s typed tree, the same way `tools/bindings/gen.py` generates `Pia.Sys.Posix`. When an LLVM bump renames a builder, adds a property or splits an op, only the mapping changes. The schema, the encoding and every artifact stay the same.

### 2. Lock-step with piac and the language

The schema version is a single integer, `kIrVersion` in `src/ir/Schema.h`. It is recorded in every certificate (format 4) next to the ABI version, and it is hashed into the module hash.

- A piac **writes** only the current schema version.
- A piac **reads** the current version and the versions still inside the deprecation window (section 4).
- CI enforces the lock-step. `tools/ir/check.py` fails a PR that makes piac emit an op, type or field the schema does not list, which a round-trip test over every `tests/verify` module catches. It also fails a PR that changes the schema without bumping `kIrVersion` and adding a migration, unless the PR says `no-ir-migration: <why>`, for example for an op that is only added. This is the same shape as ADR 0073's `tools/migrate/check.py`.
- An LLVM bump that changes an upstream op's meaning, not only its API, is a schema change like any other: a new version and a migration.

### 3. The encoding

The encoding is deterministic, so equal modules give equal bytes and a hash over the bytes is a hash over the program:

- A header: magic `PIAIR`, the schema version and the ABI version.
- A string table and a type table, each in first-use order.
- Ops in pre-order, each written as its id, then its fields in schema order. Integers are LEB128 and values are numbered in definition order.
- Locations go in a separate table, so a module's hash does not change when only its comments or layout move. The table is kept, so that diagnostics after a read still point at the source.
- zstd for shipping, not for hashing.

`piac --emit=ir` writes it, `piac --dump-ir` prints it as text for review and diffs, and `piac --from-ir` reads it.

### 4. Deprecation and migration

These follow ADR 0073 section 5, with the same window:

- **Deprecating** an op or a field marks it in the schema with the version that deprecated it and the migration that replaces it. Readers accept it for one schema version, with a `deprecated` warning naming the migration. After that window it is an error that still names the migration, forever.
- **A migration** lives in `src/ir/migrate/`: a rewrite from version N to version N+1 on the decoded tree, before mapping to MLIR. Typical ones rename an op, split a field, change an attribute's encoding, or expand an op into others. `piac migrate --ir <file>` upgrades an artifact in place, and readers apply migrations on the fly inside the window.
- **Migrations keep proofs only when they keep meaning.** Each migration is marked `preserving` or `changing`:
  - A `preserving` migration has a test: the obligations of the old and new forms are the same goals, by query hash. A certificate then carries over, recording `migrated <old module hash> <migration id>`.
  - A `changing` migration invalidates the module's proofs. The artifact must be proved again from source, and `pia-cert check` says so.

### 5. A proof table beside the IR

Each artifact carries a **proof table**: for each obligation, its stable id (the function, then the goal's index in walk order), its status, its method and the SHA-256 of its query. A reader that maps the IR back walks the same goals and takes each status from the table without solving. A goal missing from the table, or one whose query hash differs, is an error, never a silent re-proof. The table replaces the "MLIR bytecode" of abi.md's proof bundle. The table's hash and the module hash go into the certificate, so `pia-cert check` can tell that an artifact, its table and an object came from one program.

### 6. What stays text

- `.piai` interfaces stay canonical Pia source. They are what people and agents read, and the interface hash is already over that text.
- `@lower` bodies stay the MLIR text the program wrote (ADR 0065). They are trusted items whose hash the certificate already records, and their ops need not be in the schema.
- LTO (ADR 0076, section 5) stays LLVM bitcode, because it is written and read within one build and never shipped.

### 7. Portable, and readable by Pia itself

Dean (2026-11-28): "What I don't want is to be locked to MLIR's format, but I want a portable format as well. One ulterior motivation here might be if we can eventually self-host Pia so that the compiler can handle the bytecode produced to replicate what the MLIR infrastructure gives us but in Pia. That's probably a 1.0 feature."

So Pia IR is defined independently of any one implementation, piac's C++ included:

- **The spec is a document, not code.** `docs/ir.md` defines the encoding byte by byte: the header, LEB128, the tables, op and field order, and how each field type is written. The schema gives the op list. A conforming reader can be written from those two alone, in any language.
- **The schema is Pia, not TableGen.** TableGen is LLVM's. A schema in `lib/Pia/Ir/Schema.pia` is data a Pia program can read, so a self-hosted compiler loads the same table that generates piac's C++ mapping today. The schema is a module with an interface, so changing it is an interface change, and the hash and the migration check see it.
- **Portable bytes.** Integers are LEB128, floats are IEEE 754 bit patterns written little-endian, strings are UTF-8 with a length, and nothing depends on the host's word size, endianness or alignment. Target-specific facts, such as the size of `usize` or a `@place(gpu)` op, are fields with the target named, never assumptions of the encoding. A module proved for one target is readable on any host.
- **No MLIR in the definition.** The mapping to MLIR is one consumer. A self-hosted Pia that implements its own passes over Pia IR is another, and the schema's stated meaning of each op, not MLIR's, is what both must agree with.
- **Self-hosting path (1.0, not before).** `Pia.Ir`, an encoder and decoder written in Pia, proved to round-trip, as the GIF and inflate codecs are proved against their specs (ADR 0054). Then passes written in Pia over the decoded tree, each proved against the schema's meanings. ADR 0065's `@lower` and ADR 0074's library types are already moving compiler extensions into Pia, and this gives them a stable IR to work on. Nothing before 1.0 depends on it; the C++ mapping remains the implementation until a Pia one proves equal on the round-trip suite.

## Options considered

| | Pia IR schema (chosen) | Canonical expanded Pia text | MLIR bytecode |
| --- | --- | --- | --- |
| Stable across LLVM bumps | Yes: only the generated mapping changes | Yes: it is the language | No |
| Versioned by | `kIrVersion`, in lock-step with piac, with migrations | the language version and ADR 0073 | MLIR's bytecode version |
| Reading back | Decode and map: no sema or IRGen | Parse, sema and IRGen again | Decode |
| Keeps IR-level results | Yes: transforms, lowering checks, proof attributes | No, they are redone | Yes |
| Cost to build | The schema, the generated mapping, the encoder and a migration per change | A canonical printer for every node kind | None |

Canonical text was this ADR's first proposal. It loses to the schema because it throws away work the reader must redo (sema, IRGen and the transforms) and cannot carry IR that has no source form, such as the output of ScalarizeRecords or a verified `@lower` replacement. The schema keeps that, and stays ours.

## Consequences

- An LLVM bump changes the mapping code and nothing shipped. A schema change is visible, versioned and migrated, like a language change.
- Every op piac emits must be in the schema, so a new upstream op costs a schema entry with its meaning. That is a deliberate friction: it is the list of upstream semantics Pia depends on, written down.
- One release of deprecated ops is the reader's cost, the same as one release of deprecated syntax in ADR 0073.
- Hashes are over Pia's encoding, so a certificate means the same thing under every piac with the same schema and ABI versions.

## Steps

1. `lib/Pia/Ir/Schema.pia` and the byte-level spec in `docs/ir.md` for the `pia`, `pia_contract` and `pia_par` dialects and the upstream ops a `tests/verify` module uses, the generated mapping, `--emit=ir`, `--from-ir` and `--dump-ir`. The test round-trips every file in `tests/verify` and checks that the reports are identical.
2. `tools/ir/check.py` in CI: no emitted op outside the schema, and no schema change without a version bump and a migration.
3. The proof table, and `--verify --proof-table=<file>`.
4. Certificate format 4: `ir <version>`, the module hash and the proof table hash, checked by `pia-cert check`.
5. The migration framework in `src/ir/migrate`, `piac migrate --ir`, and the first migration when the first schema change lands.
6. ADR 0076's whole-program mode and transparent bodies read Pia IR.
7. (1.0) `Pia.Ir`: an encoder and decoder in Pia, proved to round-trip against `docs/ir.md`, then passes over it in Pia.
