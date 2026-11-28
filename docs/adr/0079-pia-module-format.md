# 79. Pia IR: a versioned op schema Pia controls, in lock-step with piac, with deprecations and migrations

Date: 2026-11-28

Status: Proposed. Section 3 rewritten (Dean, 2026-11-28) around four properties: compact, lossless with derived facts marked, one streaming pass, and frame-level integrity.

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

Dean set four properties for the encoding (2026-11-28), in this order: compact, lossless, read in one streaming pass, and tamper-evident. Each rule below serves one of them. Protobuf was considered and dropped, because its bytes are not canonical and hashes need them to be (Dean, 2026-11-28).

#### 3.1 Compact

- **Integers are LEB128**, signed ones zigzag-encoded first, so small values take one byte. Floats are IEEE 754 bit patterns, little-endian, since their bits do not shrink.
- **An op is its schema id, then its fields in schema order**, with no field tags or names: the schema says what comes next. A field the schema fixes (a result count, an operand count of a fixed-arity op, a result type the op's rule determines, see 3.2) is not written at all.
- **Operands are back-references.** Values are numbered in definition order, and an operand is written as the distance back from the next value to be defined, so the common case (a value used just after it is made) is one byte.
- **Strings and types are written once.** The first use of a string or a type writes it inline, and it takes the next index in its table; every later use writes the index. There is no table up front, so nothing is written twice and nothing is written before it is needed.
- **Compression is per frame** (3.4): a frame's payload may be zstd-compressed, with the dictionary in the schema, and the flag in the frame header. The hashes are over the uncompressed payload, so the compression level never changes a hash.

#### 3.2 Lossless, with derived facts written down

- **Everything piac reads back is written**: every op, field, attribute, region and block, the locations, the proof table (section 5), and the facts later stages need, such as `pia.recursive_group`, layouts and verified ranges. A module read back is the module written, which the round-trip test of step 1 checks op by op.
- **Derived facts are written and marked derived.** Some fields piac can recompute: a result type from its operands, a record's layout, a function's recursive group, a goal's query hash. The schema marks those fields `derived`. They are written anyway, so a reader can stream without inference, and a reader recomputes each one where it can and compares; a mismatch is an error naming the op, the field and both values. `piac --from-ir` checks them by default, as the strongest guarantee is the default (ADR 0004).
- **What is omitted is only what the schema fixes** (3.1), never what an analysis computed.

#### 3.3 One streaming pass, no backtracking, no forward references

The reader is a single pass that builds MLIR as it reads, with no tree in between:

- **Everything is defined before it is used.** Strings and types appear inline at first use (3.1). Values are numbered in definition order, and ops are written in an order where every operand is already defined: pre-order, with a region's blocks in dominance order.
- **A region declares its blocks first.** It starts with its block count and each block's argument types, then the blocks' ops. A branch names its successor by index among blocks already declared, so an unstructured loop or a forward jump never needs a forward reference, and a value carried around a loop is a block argument, as in MLIR.
- **A symbol is declared before it is referenced.** A call to a function defined later in the module writes a declaration record first (the name, signature and attributes), which the definition later completes; a reader creates the declaration when it meets it, as MLIR allows.
- **Lengths come first.** Every frame and every region starts with its byte length, so a reader can skip one it does not need without parsing it. The writer buffers one frame at a time to know its length.
- **The order is fixed**, so the stream is deterministic: equal modules give equal bytes.

#### 3.4 Frames, checksums and a hash chain

The stream is a sequence of frames, so corruption is caught before any of it reaches the decoder:

- **The header frame** comes first: magic `PIAIR`, the schema version, the ABI version, the target, and the frame size limit (64 KiB by default).
- **Each frame** carries its sequence number, kind (header, ops, locations, proof table, trailer), payload length, compression flag, the payload, a **CRC-32C** of the stored bytes, and a **chain digest**: SHA-256 of the previous frame's chain digest, the sequence number, the kind and the uncompressed payload. Frames break only between top-level records, so a frame decodes on its own.
- **The reader checks each frame before decoding it.** A bad CRC is corruption, and a chain digest that does not follow from the previous one is a frame that was changed, dropped, repeated or moved. Either one stops the read with the frame's number.
- **The trailer frame** ends the stream with the frame count and the final chain digest. A stream without one was truncated. The reader holds what it decoded until the trailer checks, so a truncated or tampered module never reaches codegen.
- **Two hashes come out.** The **module hash** is the chain over the frames that carry meaning, so it does not change when only locations change (locations have their own frames); the **artifact hash** is the chain over every frame. The certificate (format 4) records both, so `pia-cert check` can tie an artifact, its proof table and an object to one program, and a change to any byte shows.

CRC-32C catches accidental damage cheaply; the chain catches deliberate changes, because a forged frame needs a forged chain up to a digest the certificate already records. Signing the certificate itself is ADR 0024's concern, not this format's.

`piac --emit=ir` writes it, `piac --dump-ir` prints it as text for review and diffs, and `piac --from-ir` reads it.

### 4. Deprecation and migration

These follow ADR 0073 section 5, with the same window:

- **Deprecating** an op or a field marks it in the schema with the version that deprecated it and the migration that replaces it. Readers accept it for one schema version, with a `deprecated` warning naming the migration. After that window it is an error that still names the migration, forever.
- **A migration** lives in `src/ir/migrate/`: a rewrite from version N to version N+1 on the decoded tree, before mapping to MLIR. Typical ones rename an op, split a field, change an attribute's encoding, or expand an op into others. `piac migrate --ir <file>` upgrades an artifact in place, and readers apply migrations on the fly inside the window.
- **Migrations keep proofs only when they keep meaning.** Each migration is marked `preserving` or `changing`:
  - A `preserving` migration has a test: the obligations of the old and new forms are the same goals, by query hash. A certificate then carries over, recording `migrated <old module hash> <migration id>`.
  - A `changing` migration invalidates the module's proofs. The artifact must be proved again from source, and `pia-cert check` says so.

### 5. A proof table beside the IR

Each artifact carries a **proof table**: for each obligation, its stable id (the function, then the goal's index in walk order), its status, its method and the SHA-256 of its query. A reader that maps the IR back walks the same goals and takes each status from the table without solving. A goal missing from the table, or one whose query hash differs, is an error, never a silent re-proof. The table replaces the "MLIR bytecode" of abi.md's proof bundle. It travels in its own frames (section 3.4), after the ops it describes, so it is in the artifact hash but not the module hash: re-proving with a new prover changes the table and leaves the module hash alone. The certificate records the table's hash beside the module hash, so `pia-cert check` can tell that an artifact, its table and an object came from one program.

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
- Integrity costs 4 bytes of CRC and 32 bytes of chain digest per frame of up to 64 KiB, under 0.1%, and the reader holds its output until the trailer checks, so a truncated or tampered artifact produces nothing rather than a partial module.
- Derived fields cost bytes on disk, which is the price of checking them: a reader that trusts them would turn a corrupted layout into wrong code.

## Steps

1. `lib/Pia/Ir/Schema.pia` and the byte-level spec in `docs/ir.md` for the `pia`, `pia_contract` and `pia_par` dialects and the upstream ops a `tests/verify` module uses, the generated mapping, the frames (CRC-32C, chain digest, trailer), the one-pass reader that re-checks derived fields, `--emit=ir`, `--from-ir` and `--dump-ir`. The test round-trips every file in `tests/verify` and checks that the reports are identical, and a corruption test flips bytes, drops and reorders frames, and truncates files, and checks that each is refused with the frame named.
2. `tools/ir/check.py` in CI: no emitted op outside the schema, and no schema change without a version bump and a migration.
3. The proof table, and `--verify --proof-table=<file>`.
4. Certificate format 4: `ir <version>`, the module hash, the artifact hash and the proof table hash, checked by `pia-cert check`.
5. The migration framework in `src/ir/migrate`, `piac migrate --ir`, and the first migration when the first schema change lands.
6. ADR 0076's whole-program mode and transparent bodies read Pia IR.
7. (1.0) `Pia.Ir`: an encoder and decoder in Pia, proved to round-trip against `docs/ir.md`, then passes over it in Pia.
