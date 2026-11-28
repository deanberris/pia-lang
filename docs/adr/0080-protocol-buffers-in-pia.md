# 80. Protocol Buffers in Pia: a metaprogram that turns `.proto` into proved types and codecs, and Pia IR as a protobuf schema

Date: 2026-11-28

Status: Proposed

## Context

[ADR 0079](0079-pia-module-format.md) defines Pia IR: a versioned op schema in Pia, a generated mapping to MLIR, and an encoding of Pia's own made of LEB128 integers, numbered fields and length-prefixed strings. Dean then asked (2026-11-28): "How hard would it be for us to just use protobufs for the IR? Let's jump the queue and implement a protobuf metaprogram that generates the types, operations, interfaces, so that we can just encode it in a forward compatible way?"

Three facts make this a small step:

- **ADR 0079's encoding is already most of the protobuf wire format.** A protobuf varint is LEB128, a field is a number with a wire type, and strings and nested messages carry their length. Using protobuf costs little, and gains a schema language anyone can read, readers in every language through `protoc`, and evolution rules that are well understood.
- **The 0.2.0 roadmap needs the same metaprogram.** Its gRPC plugin generates Pia from `.proto`: message types, a Protocol Buffers theory, a model per message, and proved codecs, with services as interfaces. Building it now for the IR means building it once.
- **Pia already derives proved codecs from types.** `derive_json` ([ADR 0045](0045-json-derived-codecs-and-conforming-dom.md), [meta.md](../meta.md#derives)) reads a type with metaprogram builtins and writes a reader and a writer that prove. A protobuf generator has the same shape, but its input is a `.proto` file instead of a Pia type.

Protobuf also leaves four things open that a proved IR needs:

1. **Its forward compatibility is syntactic.** A reader skips a field it does not know, which is right for metadata and wrong for an op: skipping an op changes the program.
2. **Its bytes are not canonical.** The protobuf spec does not fix a serialisation: field order, packed or unpacked repeated fields, default values written or left out, and unknown fields all vary between writers. ADR 0079 hashes modules over their bytes.
3. **Nesting is bounded.** Common parsers stop at about 100 nested messages, and regions nest ops inside ops without a bound.
4. **The runtime is large.** The protobuf C++ library is BSD-licensed, so it is allowed (no GPL), but it is a big dependency for piac to carry.

## Decision

### 1. `Pia.Proto`: the wire format, proved

`Pia.Proto.Wire` implements the wire format, as `Pia.Text.Json` does JSON:

- Varints (up to 10 bytes for 64 bits), zigzag for `sint32` and `sint64`, little-endian `fixed32` and `fixed64`, and IEEE 754 bit patterns for `float` and `double`.
- Tags (`field << 3 | wire_type`), and length-delimited fields for `string`, `bytes`, nested messages and packed repeated fields.
- Skipping one field of each wire type, which is what unknown-field handling needs.

Each reader is proved never to read past its input, to reject an overlong or overflowing varint, and to round-trip with its writer (`read (write v) = v`). A `string` is checked for UTF-8 as it is read, so it arrives as Pia's `str` ([ADR 0040](0040-cpp23-standard-library-in-pia.md), section 7).

### 2. The `.proto` metaprogram

`Pia.Proto.Gen` exports a metaprogram that takes a proto3 file and returns items:

```ocaml
import Pia.Proto.Gen.Gen as P
P.generate (read_text "ir/ir.proto")
```

- **Types.** A `message` becomes a record. A field becomes a record field of the matching Pia type (`int32` becomes `i32`, `uint64` becomes `u64`, `bool`, `string` and `bytes` as above). A `repeated` field becomes a `vec` with the allocator ADR 0026 requires, an `optional` field becomes an `option`, a `oneof` becomes a variant, an `enum` becomes a variant with its numbers kept as a range type for unknown values, and nested messages become records named `Outer_Inner`.
- **Codecs.** For each message: `write_<m>`, which writes it, with room stated in its precondition as `derive_json`'s writers do, and `read_<m>`, which reads it into a fully initialised value, with errors in a closed set (`Truncated_<m>`, `WireType_<m>`, `Utf8_<m>`, `Range_<m>`, `Missing_<m>` for a required field, see section 4). It dispatches on field numbers with a decision tree built at compile time.
- **Services.** A `service` becomes a Pia interface ([ADR 0039](0039-module-and-interface-syntax.md)), one function per RPC, from request to `result` of response. 0.2.0's gRPC transport implements it.
- **Options as attributes.** Protobuf options the generator understands (`deprecated`, and the Pia options of section 4) become attributes on the generated items. Others are kept as attributes and ignored.

The metaprogram is ordinary Pia that runs in the interpreter. Its `.proto` parser uses the builtins metaprograms already have (`bytes`, string compare, lists). It needs one more builtin: **`read_text path`**, which returns a file's contents as a string at expansion time. The file is resolved hermetically, with the same roots and flags as `@embed` ([ADR 0070](0070-raw-binary-embedding.md), section 2), and its hash goes into the module's interface hash, so a changed `.proto` rebuilds its importers. It is a metaprogram builtin with no run-time form, not a language builtin.

### 3. A theory of Protocol Buffers, and a model per message

`Pia.Proto.Theory` states the encoding as a spec: a message is a finite map from field numbers to lists of values, encoding is a function of that map, and decoding follows protobuf's rules. The last value wins for a singular field, repeated values are concatenated, packed and unpacked forms both decode, and unknown fields are skipped or kept. The generated code is proved against it:

- `decode (encode m) = m` for every generated message.
- `decode` accepts every encoding of `m` that the protobuf spec allows (any field order, packed or unpacked, defaults written or left out), not only the canonical one.
- `canonical m` (section 5) is a function of `m`'s value alone.

These are the lemmas 0.2.0's gRPC work needs as well, so they are written once here.

### 4. Forward compatibility that keeps meaning

Protobuf's skip-unknown rule is kept for fields that cannot change meaning, and made an error for those that can:

- **Must-understand by default.** In a schema marked `option (pia.strict) = true;`, as Pia IR is, a reader that meets an unknown field number or an unknown `oneof` case is an error that names the number, the message and the schema version that introduced it, if the reader knows it. An unknown op is always this error.
- **Advisory fields.** A field marked `[(pia.advisory) = true]` (locations, debug names, optimisation hints, extra proof-table data) is skipped when unknown, and preserved when the message is re-written.
- **Required fields.** `[(pia.required) = true]` makes a missing field `Missing_<m>`, which protobuf 3 cannot express on its own.

Outside strict schemas, as for gRPC messages, the generator follows plain proto3 rules.

### 5. A canonical form for hashing

A Pia writer always writes the **canonical form**: fields in ascending number order, repeated scalars packed, default values of fields without presence left out, no unknown fields, and map entries (if a schema uses `map`) sorted by key. Hashes, certificates and the module hash of ADR 0079 are over canonical bytes. A reader accepts any valid encoding, and before it checks a hash it re-encodes canonically and hashes that. Section 3 proves the canonical form is a function of the value, so equal programs hash equal however their bytes were written.

### 6. Pia IR as a protobuf schema (amends ADR 0079)

- **Section 1 (the schema).** The IR schema is `lib/Pia/Ir/ir.proto`, in strict mode. An op is a message, and its stable numeric id is its field number in the `Op` `oneof`, never reused (protobuf's `reserved` enforces that). A type is a message in a `Type` `oneof` in the same way. Each op's meaning is a doc comment on its message. `Pia.Proto.Gen` reads the file to make Pia's types for it, and `tools/ir/gen` reads it to make piac's C++ codec and the MLIR mapping, so there is one schema. This replaces `lib/Pia/Ir/Schema.pia`, pending Dean's choice of source of truth.
- **Section 3 (the encoding).** The encoding is protobuf's wire format in the canonical form of section 5. A module is a `Module` message: a header (magic `PIAIR` in field 1, the schema version, the ABI version), a string table, a type table, an **op table**, and a separate location table, which is an advisory field. Regions do not nest messages: a region lists the indices of its blocks, and a block the indices of its ops in the op table, so the message depth stays constant however deep the program nests. Values are numbered in definition order, as before. zstd is still for shipping, not for hashing.
- **Section 7 (portable).** `docs/ir.md` still specifies the format, now as `ir.proto` plus the canonical-form rules and the table layout. Any language with a protobuf library can read Pia IR. The self-hosting path is unchanged, and gets shorter: `Pia.Ir`'s encoder and decoder are the ones this metaprogram generates, proved by section 3.
- **piac carries no protobuf runtime.** `tools/ir/gen` writes a small wire reader and writer in C++ from `ir.proto`, the same way it writes the mapping. `protoc` and its C++ library are used only in tests: CI decodes piac's output with protoc-generated code and compares the canonical bytes both ways.
- **Unchanged.** `kIrVersion`, deprecation for one schema version, migrations marked `preserving` or `changing`, the proof table and `tools/ir/check.py` all stay as ADR 0079 decides. Protobuf's compatibility rules are the floor (never reuse a field number, never change a field's type); `kIrVersion` and a migration are still required for any change in meaning.

## Options considered

| | Protobuf schema and wire format (chosen) | ADR 0079's own encoding | FlatBuffers or Cap'n Proto |
| --- | --- | --- | --- |
| Readers outside Pia | Every language, through protoc | Only ones written from `docs/ir.md` | Many, through their compilers |
| Forward compatibility | Skip-unknown for advisory fields, strict for the rest (section 4) | Version and migrations only | Built in, but no must-understand fields |
| Canonical bytes | A canonical form we define and prove (section 5) | Deterministic by construction | Not canonical (vtables, padding) |
| Reuse for 0.2.0 gRPC | The same metaprogram and theory | None | None: gRPC uses protobuf |
| Cost | Wire module, metaprogram, theory, `read_text` | The encoder and decoder only | A new format with no 0.2.0 reuse |

## Consequences

- Pia IR becomes readable with off-the-shelf tools, and the `.proto` metaprogram that 0.2.0 needs is built now, against a demanding first user.
- The ops Pia depends on are still written down one by one with their meanings, now as protobuf messages.
- Strict mode means an old piac refuses a newer module instead of misreading it, as ADR 0079 intends; protobuf's laxer rules apply only where they are safe.
- `read_text` makes a metaprogram's output depend on a file, and the interface hash records it.

## Steps

1. `Pia.Proto.Wire`, proved: varints, zigzag, fixed-width numbers, tags, length-delimited fields and skipping, prototyped in the REPL first, with `tests/std/proto_wire.pia`.
2. `read_text` in the metaprogram interpreter, hermetic like `@embed`, with its hash in the interface hash.
3. `Pia.Proto.Gen` for messages of scalars, `string`, `bytes`, nested messages, enums and `repeated`: types, writers and readers that prove, and a C round trip against protoc-generated code.
4. `oneof`, `optional`, `map`, and the Pia options of section 4.
5. `Pia.Proto.Theory` and the lemmas of section 3; the canonical form of section 5.
6. `lib/Pia/Ir/ir.proto` for the ops of ADR 0079 step 1, `tools/ir/gen` writing the C++ codec, and the protoc cross-check in CI.
7. Services as interfaces, for 0.2.0's gRPC transport.
