# 45. JSON: derived streaming codecs, typed construction, and a DOM proved to conform to a type

Date: 2026-11-22

Status: Proposed

## Context

Dean asked (2026-11-22) for a standard JSON serialiser and deserialiser in three parts:

1. **Metaprograms generate the efficient streaming code.** Serialisation was a stated day-one use of metaprograms ([ADR 0007](0007-metaprogramming-fixed-point-expansion.md), [design.md](../design.md)): `@derive(serialise, deserialise)` was always the plan, and a derived reader "also emits the refinement checks, so a parsed value is proved to meet its type's invariants".
2. **Object creation that instantiates an instance of a type** straight from JSON text, without building a tree first.
3. **A generic DOM that is provably structurally consistent with a type.** Types are values in Pia, so "this document has the shape of `t`" can be a predicate over a type value and a document, and a document that satisfies it converts to `t` without a failure path.

Constraints from earlier decisions:

- Errors are closed sets with `?` and handlers ([ADR 0028](0028-error-propagation-and-cleanup.md)). There are no exceptions and no catch-all error type.
- Every allocation goes through an explicit `Pia.Mem` allocator and can fail with `OutOfMemory` ([ADR 0026](0026-memory-manager.md), [ADR 0041](0041-allocator-semantics-as-a-theory.md)); `vec` stores its allocator (Dean, 2026-11-22). No garbage collection.
- Text is UTF-8 only: `str` is `[u8]` refined to valid UTF-8 and `string` is a `vec u8` with the same invariant ([ADR 0040](0040-cpp23-standard-library-in-pia.md), section 7).
- Tuples are a core type, and a tuple type is a type list for variadic code ([ADR 0040](0040-cpp23-standard-library-in-pia.md), section 9).
- The strongest guarantee is the default ([ADR 0004](0004-strongest-guarantee-by-default.md)). Fewer keywords is better.
- Build time is a tracked benchmark ([ADR 0032](0032-parallel-sliced-cached-proving.md)): derived proofs must stay small and per-type, and must not grow one query per program.

### Prior art

- **Rust serde + serde_json** separate the data model (a visitor over a fixed set of kinds) from formats, and derive `Serialize`/`Deserialize` per type. Attributes rename fields, choose a variant tagging (external by default, internal, adjacent, untagged), deny unknown fields and supply defaults. `serde_json::Value` is the untyped tree, and `from_value` turns it into a type, failing at run time if the shapes disagree.
- **simdjson** finds structural characters with SIMD in a first stage and writes a flat *tape* in a second: each container records where it ends, so skipping a subtree is one jump and the DOM is one allocation. Its On-Demand API parses lazily into the caller's types.
- **RapidJSON** and **Boost.JSON** offer both a SAX-style push parser and a DOM; **glaze** and **Boost.Describe** use compile-time reflection to generate per-type readers with perfect-hash key matching.
- **Go `encoding/json`**, **aeson** (Haskell, `Generic` deriving), **ppx_yojson_conv** (OCaml) and **Zig `std.json`** (`parseFromSlice(T, ...)`, a type as an argument) all derive codecs from type structure.
- **JSON Schema** and **TypeScript type guards** (`x is T`) state shape as a checkable predicate, but nothing proves the check matches the conversion that follows. **F# type providers** go the other way, from a sample document to a type.
- **RFC 8259** is the grammar. **I-JSON (RFC 7493)** is the interoperable subset: valid UTF-8, no lone surrogates, unique member names, numbers within IEEE double range.

What none of these give is a proof. serde's `from_value` and a hand-written type guard can disagree with each other and with the writer; a Pia library can prove that they agree.

## Decision

### 1. One module family, one specification

The library is `Pia.Text.Json`, in `lib/Pia/Text/Json/`, one module per file ([ADR 0039](0039-module-and-interface-syntax.md)):

| Module | Provides |
| --- | --- |
| `Json.Spec` | the grammar of RFC 8259 as spec functions over bytes (`valid s`, `value_at s i j`), and the meaning of a number literal as an `int` or `real` |
| `Json.Lex` | a streaming tokenizer over a byte slice: proved to accept exactly the RFC 8259 token language, with every string token proved valid UTF-8 after unescaping |
| `Json.Write` | a writer of tokens into an output buffer or a `vec u8`, proved to produce `Json.Spec.valid` UTF-8 |
| `Json.Derive` | the `@derive(json)` metaprogram and the `Json` concept |
| `Json.Dom` | the untyped document (section 5) and its builder |
| `Json.Shape` | `conforms`, `check` and `from_dom` (section 6) |

Everything is stated against `Json.Spec`, so the lexer, the writer, the derived codecs and the DOM are proved against one grammar rather than against each other.

### 2. Derived streaming codecs

`@derive(json)` on a type item generates a writer and a reader for it, as `@derive(eq)` generates `eq_<name>` today ([meta.md](../meta.md#derives)):

```ocaml
let point = type { x : i32; y : i32 } @derive(json)

let shape = type
  | Circle of { r : u16 }
  | Rect of { w : u16; h : u16 }
  | Empty
  @derive(json)
```

For each type the derive emits:

- `write_json_<t> (w : borrowed inout mutable writer) (v : t) : result unit write_error`, which streams tokens without building anything, and whose postcondition says the bytes it appended are `Json.Spec.valid` and denote `v`;
- `read_json_<t> (l : borrowed inout mutable lexer) ... : result t (json_errors t)`, which pulls tokens and builds the value as it goes, with no intermediate tree.

What makes them efficient is that they are generated per type, not interpreted:

- **Keys are matched by a decision tree the metaprogram builds at compile time** from the field names: a switch on the key's length, then on the first byte where the remaining candidates differ, then one comparison against the whole name. An unknown key is found with no hashing and no allocation.
- **Fields are written in declaration order with their keys as constants**, so a writer is a sequence of stores of literal bytes and integer formatting.
- **Integers are parsed directly into their range type**, with the range check fused into the digit loop: a `u8` field reads at most three digits.
- **Strings without escapes are borrowed from the input** (section 4); only strings with escapes, or `string` fields, copy.
- **Nested types call each other's readers**, which codegen inlines, so a record of records is one loop over the tokens.

Defaults follow ADR 0004, strictest first, with attributes to relax them (attributes, not keywords):

| Situation | Default | Attribute |
| --- | --- | --- |
| Member name | the field's name | `@json(name = "x")` |
| Unknown member | error `Unknown` | `@json(ignore_unknown)` on the type |
| Missing member | error `Missing`, unless the field is an `option` | `@json(default = v)` |
| Duplicate member | error `Duplicate` (I-JSON) | none |
| Variant | externally tagged: `{"Circle": {"r": 3}}`, and a constructor without payload as the string `"Empty"` | `@json(tag = "kind")` for internal tagging of record payloads |
| Record field with `where` | checked after the record is read; failure is `Invalid` | none |

Each reader tracks which fields it has seen in a bit set and proves, at the closing brace, that every required field was set exactly once, so the record it returns is fully initialised by construction.

**Error sets are exact per type.** `json_errors t` is a type-level metaprogram ([ADR 0035](0035-substitution-failure-and-total-constraints.md)) that computes the closed set a reader of `t` can raise, as an error set union ([#84](https://github.com/deanberris/pia-lang/issues/84)): every reader can raise `Syntax of pos`, but `Range` only if `t` contains an integer narrower than the literal allows, `Invalid` only if it contains a `where`, `OutOfMemory` only if it contains a `string` or a `vec`, and `Depth` never for a type that is not recursive, because the nesting a reader accepts is bounded by the type's own depth. A handler for `read point` therefore lists four errors, not twelve, and the compiler checks the list is exact.

### 3. Typed construction: the type is an argument

A program asks for an instance of a type by passing the type, since types are values:

```ocaml
let load (text : str) : result point (json_errors point) =
  let p = Json.read point text? in
  Ok p

let load_all (a : borrowed inout mutable pool) (text : str)
  : result (vec point) (json_errors (vec point)) =
  Json.read (vec point) text a
```

- `Json.read (t : type) (s : str) ...` is a generic function constrained on the concept `Json t`, which `@derive(json)` instantiates, and which the prelude provides for `bool`, the integer and range types, `str`, `string`, `option t`, `vec t`, fixed arrays `[t; n]` (the array's length is checked) and tuples. A JSON array of mixed kinds reads into a tuple type, `(u8, str, bool)`, element by element: that is where variadic shapes come from, with no variadic machinery beyond tuple types.
- The allocator parameter appears only when `t` needs one. That is decided by a type-level metaprogram, `needs_alloc t`, so `Json.read point text` takes none and cannot fail with `OutOfMemory`.
- `Json.read_into (t : type) (s : str) (dst : out t)` builds the value in place, for large arrays and records the caller has already placed (an arena, a buffer of records). The `out` rules ([ADR 0005](0005-parameter-modifiers.md)) prove `dst` is fully written on success.
- `Json.write (v : t) (w : ...)` and `Json.to_string (v : t) a` are the writing side.

The concept states the laws that make the two directions one codec ([ADR 0034](0034-concepts-and-overload-resolution.md)):

```ocaml
let meta Json (t : type) : concept = sig
  let write_json : borrowed inout mutable writer -> t -> result unit write_error
  let read_json  : borrowed inout mutable lexer -> result t (json_errors t)
  (** Writing then reading gives back the same value. *)
  let law round_trip (v : t) : read_json (lexer_of (encode v)) = Ok v
end
```

`encode` is the spec function that the writer's postcondition is stated with. A derived instance proves `round_trip` from its fields' instances, one lemma per field, so the proof is linear in the number of fields and never unfolds a nested type's codec ([ADR 0043](0043-generic-definitions-proved-once.md)).

### 4. UTF-8 and strings

- Input is `str`, or `[u8]` that the lexer validates first. Outside string literals JSON is ASCII, so validation only runs inside strings, and every string token the lexer hands out is proved valid UTF-8.
- `\uXXXX` escapes are decoded, surrogate pairs are joined, and a lone surrogate is a `Syntax` error (I-JSON). The writer escapes `"`, `\` and the control characters, and writes everything else as UTF-8, so its output is valid UTF-8 and valid I-JSON.
- A `str` field borrows from the input when the literal has no escapes: its result type is `borrowed(s)` ([#70](https://github.com/deanberris/pia-lang/issues/70)), so the value cannot outlive the text. A literal with escapes needs somewhere to put the unescaped bytes, so a `str` field reads through an arena the caller passes, and a `string` field copies into its own allocator.

### 5. The DOM is a tape, generic over its storage

The untyped document is a flat tape in the style of simdjson, not a tree of boxes:

```ocaml
let kind = type | Null | False | True | Num | Str | Arr | Obj
let node = type { kind : kind; a : u32; b : u32 }   (* Arr/Obj: index past the end, member count; Str/Num: byte range *)
let dom = type { nodes : vec node; text : str }      (* text: the input, or an arena holding unescaped strings *)
```

- **Why a tape.** A tree of variants needs recursive types, which Pia does not have yet, and, without a garbage collector, every box would be a separate allocation that the program must free. A tape is one `vec` (which stores its allocator), freed by one `drop`; a subtree is a range of indices, so skipping one is a jump and walking one is a loop. It is also the fastest layout known for this job.
- **Its invariant is a spec function**, `well_formed d`, stated with quantifiers over indices: every container's end index is inside the tape and after the container, containers nest properly, member keys are `Str` nodes, and every `Str` and `Num` range lies in `text` and is valid there. `Json.Dom.parse` ensures `well_formed`, and the builder's functions (`push_null`, `begin_obj`, `key`, `end_obj` and so on) require and preserve it, so a program can also build a document by hand.
- **Numbers are kept as their literal text**, proved to match the grammar, with their value given by the spec function `Json.Spec.number_value : str -> real`. Nothing is rounded until a typed conversion asks for an integer (exact) or, once floats exist, a float.
- **"Generic"** means the DOM is the same for every document and every target type, and is parameterised only by where its memory comes from. **"Variadic"** content (arrays of mixed kinds, objects with any members) needs nothing more: it is just nodes.

### 6. A DOM proved to conform to a type

Since types are values, conformance is a function of a type and a document:

```ocaml
(* Spec: the subtree at node i has the shape of t. *)
let spec conforms (t : type) (d : dom) (i : u32) : bool
```

It is defined by a type-level `match` on `t`, one arm per kind of type, and recursion on the *type*, not on the document: `[e]` and `vec e` require every element of the array at `i` to conform to `e`; a record requires an object with exactly its required members, each conforming to its field's type, and its `where` to hold of the values they denote; a range type requires a `Num` whose `number_value` is an integer in the range; a tuple type requires an array of exactly that length whose elements conform position by position; `option e` allows `Null`. Types are finite trees, so `conforms` is total by the structural rule of ADR 0035 without a measure, and for a given `t` it unfolds into a fixed, finite formula.

Three functions use it, generated per type by `@derive(json)` and called through the concept:

```ocaml
let check (t : type) (d : borrowed dom) (i : u32) : bool
  requires well_formed d
  ensures result <==> conforms t d i

let from_dom (t : type) (d : borrowed dom) (i : u32) : or_oom t   (* t, or result t oom if t allocates *)
  requires well_formed d && conforms t d i

let to_dom (t : type) (v : t) (a : ...) : result dom oom
  ensures (match result with | Ok d -> well_formed d && conforms t d 0 | Err _ -> true)
```

- **`from_dom` cannot fail on shape.** Its precondition is the conformance, so the only error left is `OutOfMemory`, and only if `t` holds a `string` or a `vec`. Its result type is the type-level metaprogram `or_oom t`, which is `result t oom` for such a `t` and plain `t` otherwise, so for most types there is no error path to handle at all. A program proves `conforms` either by calling `check` and branching on it, or by having built the document with `to_dom`, or from any other fact that implies it:

```ocaml
let get_point (d : borrowed dom) : option point
  requires well_formed d
= if Json.check point d 0 then Some (Json.from_dom point d 0) else None
```

- **The three paths agree**, as a law of the concept: reading `t` from text gives `Ok v` exactly when parsing the text gives a document `d` that conforms to `t` and `from_dom t d 0 = v`. So a program may stream, or parse once and convert several times, and get the same values and the same accepted inputs either way.
- **Branded documents come later.** Once refinements on values work ([status.md](../status.md)), `conforming t` will be a type, `{ d : dom where well_formed d && conforms t d 0 }`, so the proof travels with the value across function and module boundaries instead of as a `requires` on each function. Until then the precondition form is the same proof with more writing.

### 7. Streaming input, depth and speed

- **The lexer is a state machine**, stated with the prelude's `machine` theory ([theories.md](../theories.md#state-machines)), and keeps no state outside its record. So it can stop at the end of one chunk and resume with the next, which is what streaming from a file or socket needs. The first version works over a complete slice; chunked input arrives with `Pia.Io`'s `reader` concept, and a pull reader as a coroutine with [ADR 0027](0027-coroutines-and-race-freedom.md).
- **Depth.** Derived readers of non-recursive types need no depth limit (section 2). `Json.Dom.parse` takes a maximum depth as a range-typed argument and keeps its container stack in a fixed-size array, so it never recurses and its stack use is a proved constant.
- **SIMD.** The first lexer is scalar. A structural-character scanner in the style of simdjson's first stage comes with `vec<T, k>` (M10), proved against the same `Json.Spec`, so nothing above the lexer changes.

### 8. What this ADR does not decide

- Floating-point numbers. Until floats exist (M11), numbers read into integer and range types (exactly) or stay as literal text. `f32` and `f64` fields then need a correctly rounded decimal conversion proved against real arithmetic ([ADR 0038](0038-float-kernels-against-real-theories.md)), which is its own piece of work.
- JSON Schema import and export. A metaprogram could generate a schema from a type, or a type from a schema, but neither is needed here.
- Other formats. The derive is JSON-specific. A serde-style format-independent data model can be factored out once a second format (CBOR, MessagePack, the PNG chunk readers of M13) exists to test it against.

## Gaps this depends on

These are listed, not worked around:

| Gap | What waits on it |
| --- | --- |
| `str` and `Pia.Core.Utf8` (C++23 library thread, phase 1) | every string token, and the lexer's UTF-8 proof |
| `string` and `vec` storing its allocator (`Pia.Mem` and Vec thread, #86, #72) | `string` and `vec t` fields, the DOM's node array |
| Metaprogram builtins `attrs`, `variants`, `int_bounds` and string bytes in metaprograms ([stdlib.md](../stdlib.md), section 11) | `@json(...)` attributes, variant codecs, fused range checks, key decision trees |
| Generic types and concepts in interfaces ([ADR 0039](0039-module-and-interface-syntax.md) step 3, in progress) | importing `Json` from `lib/Pia/Text/Json` into other modules |
| Core tuples (own ADR, per ADR 0040 section 9) | tuple codecs and mixed-kind arrays |
| Value refinements (`where` on values) | branded `conforming t` documents (section 6) |
| Lifetime markers on results ([ADR 0042](0042-lifetimes-liveness-and-escape-analysis.md)) | zero-copy `str` fields borrowed from the input |
| Recursive types | user types that contain themselves (trees, linked lists) cannot `@derive(json)`; a recursive spec view of the DOM, which would make some proofs shorter |
| Floats (M11) | float fields (section 8) |
| `Pia.Io` readers and writers | chunked streaming from files and sockets |
| `vec<T, k>` (M10) | the SIMD scanner |

The order below starts with what needs none of them.

## Implementation order

1. **`Json.Spec` and `Json.Lex` over `[u8]`**: tokens, positions, escapes and UTF-8 validation (with a minimal local UTF-8 spec if `Pia.Core.Utf8` has not landed), proved memory safe, terminating and accepting exactly the token grammar.
2. **`Json.Write`** into a caller's `out [u8]` with a proved capacity, then into `vec u8`; escaping and integer formatting proved against `Json.Spec`.
3. **The metaprogram builtins** the derive needs (`attrs`, `variants`, `int_bounds`, string bytes).
4. **`@derive(json)` for records of integers, bools and fixed arrays**: readers with key decision trees, seen-field sets, fused range checks and exact error sets; writers; `Json.read t`.
5. **Variants, `option`, `vec`, `str` and `string`**, then tuples once core tuples land.
6. **`Json.Dom`**: the tape, `well_formed`, `parse` with a bounded stack, and the builder.
7. **`Json.Shape`**: `conforms`, `check`, `from_dom` and `to_dom`, per type.
8. **The laws**: `round_trip`, and agreement between streaming and DOM paths, proved per derived type from per-field lemmas, with `proof_bench` watching their cost.
9. **A literate page, `docs/json.pia.md`**, with every example doc-tested, and the C++ map updated (`nlohmann::json` and Boost.JSON have no `std` header, so it gets a row under "beyond the standard").
10. **Chunked streaming** over `Pia.Io`, and the SIMD scanner with M10.

## Consequences

- JSON is the first full use of derives beyond `eq`, so it exercises the metaprogram builtins, error-set unions, type-level metaprograms, concepts with laws and allocators together. Gaps it hits are fixed in the core, not in the library.
- A program that reads JSON into a type gets, from the type alone, a reader that cannot index out of bounds, cannot accept malformed or non-UTF-8 input, returns only fully initialised values that meet the type's refinements, and reports exactly the errors that type can produce.
- Strict defaults (unknown and duplicate members rejected) mean some real-world documents need `@json(ignore_unknown)`. That is the intended trade: the relaxation is visible in the type's source.
- The tape DOM is less convenient to mutate than a tree. Edits that change a subtree's size rebuild that part of the tape. Convenience views over it are library functions, and a recursive tree can be added once recursive types exist.
- Proof cost grows with the number of derived types and their fields, linearly by construction. Derived proofs go in the benchmark corpus from step 4.

## Questions for Dean

1. **DOM representation.** A flat tape now (recommended: one allocation, fast, no recursive types needed), or wait for recursive types and make the DOM a tree of variants?
2. **Variant encoding.** Externally tagged by default, `{"Circle": {"r": 3}}`, with `@json(tag = "kind")` for internal tagging (recommended: it works for any payload, as serde's default does), or internally tagged by default?
3. **Strictness.** Reject unknown and duplicate members by default, with `@json(ignore_unknown)` to relax the first (recommended, per ADR 0004), or accept unknown members by default as most libraries do?
4. **Numbers before floats.** Integers and range types read exactly, and everything else stays as literal text with a `real` meaning, until M11 (recommended), or should float support move ahead of this library?
