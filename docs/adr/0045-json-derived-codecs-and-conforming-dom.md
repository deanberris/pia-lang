# 45. JSON: derived streaming codecs, typed construction, and a DOM proved to conform to a type

Date: 2026-11-22

Status: Accepted (Dean, 2026-11-22), with his answers to the four questions, which changed sections 2, 5, 6 and 8; see "Dean's answers" at the end.

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
| Member name | the field's name, and nothing else: a constructor's or type's name never appears in the output | `@json(name = "x")` on the field, as serde's `rename` and Go's `json:"x"` tag |
| Unknown member | error `Unknown` | `@json(ignore_unknown)` on the type |
| Missing member | error `Missing`, unless the field is an `option` | `@json(default = v)` |
| Duplicate member | error `Duplicate` (I-JSON) | none |
| Variant | untagged, told apart by structure: `{"r": 3}` is a `Circle` and `{"w": 2, "h": 1}` a `Rect`; the derive must prove that no document conforms to two constructors, or it is a compile error that suggests a tag | `@json(tag = "kind")` on the type, an explicit tag member whose value names the constructor (its name, or `@json(name = "c")` on the constructor) |
| Record field with `where` | checked after the record is read; failure is `Invalid` | none |

**Variants are disambiguated by structure or by an explicit tag, never by a name the type did not ask for.**

- *By structure.* For each pair of constructors, the derive proves that their shapes are disjoint: `not (conforms A d i && conforms B d i)` for every document (section 6). Most pairs are settled without the solver, because their payloads have different JSON kinds (a number and an object), or both are objects and each has a required member the other does not allow (unknown members are rejected, so that member decides). Anything else goes to the solver, as one small goal per pair. If a pair cannot be proved disjoint, such as two constructors with the same payload, or two constructors without payload, the derive fails and names the pair, and the fix is a tag. The streaming reader does not backtrack: it reads an object's members into slots for the union of the constructors' fields, and picks the constructor at the closing brace from the members it saw, which the disjointness proof says determine it. A member whose type differs between constructors keeps its raw slice of the input until the constructor is known, then parses it, which costs nothing because every token is already a slice of the input.
- *By tag.* `@json(tag = "kind")` writes `"kind": "Circle"` as the first member of the payload object, and the reader accepts the tag anywhere among the members. A constructor without payload is then `{"kind": "Empty"}`. The tag member's name and values are written in the type's source, as Dean asked, so nothing about the encoding is implicit.

Each reader tracks which fields it has seen in a bit set and proves, at the closing brace, that every required field was set exactly once, so the record it returns is fully initialised by construction.

**Error sets are exact per type.** `json_errors t` is a type-level metaprogram ([ADR 0035](0035-substitution-failure-and-total-constraints.md)) that computes the closed set a reader of `t` can raise, as an error set union ([#84](https://github.com/deanberris/pia-lang/issues/84)): every reader can raise `Syntax of pos`, but `Range` only if `t` contains an integer narrower than the literal allows, `Invalid` only if it contains a `where`, `OutOfMemory` only if it contains a `string` or a `vec`, and `Depth` only for a recursive type ([ADR 0047](0047-recursive-sum-types-and-shared-references.md)), because for any other type the nesting a reader accepts is bounded by the type's own depth. A handler for `read point` therefore lists four errors, not twelve, and the compiler checks the list is exact.

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

### 5. The DOM is a recursive sum type over slices of the input

The untyped document is an ordinary recursive variant, declared with the explicit recursion of [ADR 0047](0047-recursive-sum-types-and-shared-references.md), and every leaf is a slice of the input text:

```ocaml
let rec json = type
  | Null
  | Bool of bool
  | Num of str               (* the literal, as it appears in the input *)
  | Str of str               (* the literal between the quotes, escapes intact *)
  | Arr of vec json
  | Obj of vec (str, json)   (* members in input order; keys as raw literals *)
```

- **Backed by the input.** Parsing copies no text. A `Num` or `Str` is the exact range of the input it was read from, so a whole document is `borrowed(s)` from its text `s` ([#70](https://github.com/deanberris/pia-lang/issues/70), [ADR 0042](0042-lifetimes-liveness-and-escape-analysis.md)) and cannot outlive it. `Json.Dom.text (v : str) (out : out [u8])` unescapes a string literal on demand into a buffer the caller supplies, and `Json.Dom.eq_key` compares a raw key with a name without unescaping when the key has no escapes (the common case).
- **Recursion is explicit.** `let rec` marks the type recursive, and the recursive occurrences sit inside `vec`, an indirection that owns its elements, as ADR 0047 requires. The only allocations are the `vec`s of arrays and objects. A document is usually parsed into an arena ([ADR 0026](0026-memory-manager.md)), so it is freed by one release however many containers it holds, but any allocator works, since `vec` stores its own.
- **Its invariant is a spec function.** Since `json` is a datatype, the verifier encodes it as a Z3 datatype, and `Json.Dom.parse` ensures `valid_dom v`, a spec function defined by structural recursion on `v`: every `Num` matches the number grammar, every `Str` is a well-formed literal (valid UTF-8, legal escapes, no lone surrogates), and no object has two equal keys. A program can also build a document by hand with the constructors, and `valid_dom` says what it must meet to be written out.
- **Numbers keep their literal text**, with their value given by the spec function `Json.Spec.number_value : str -> real`. A typed conversion to an integer is exact; conversion to floats waits for floats (section 8).
- **"Generic"** means one `json` type for every document and every target type. **"Variadic"** content (arrays of mixed kinds, objects with any members) needs nothing more: it is just constructors.
- **Depth.** `Json.Dom.parse` takes a maximum depth as a range-typed argument, so its recursion is bounded and its stack use is proved, and `Depth` is in its error set.

### 6. A DOM proved to conform to a type

Since types are values, conformance is a function of a type and a document:

```ocaml
(* Spec: the subtree at node i has the shape of t. *)
let spec conforms (t : type) (v : json) : bool
```

It is defined by a type-level `match` on `t`, one arm per kind of type: `[e]` and `vec e` require `v` to be an `Arr` whose every element conforms to `e`; a record requires an object with exactly its required members, each conforming to its field's type, and its `where` to hold of the values they denote; a range type requires a `Num` whose `number_value` is an integer in the range; a tuple type requires an array of exactly that length whose elements conform position by position; `option e` allows `Null`; a variant requires that `v` conform to one of its constructors (to exactly one, by the disjointness proof of section 2), with its tag member if it has one. For a non-recursive `t`, recursion is on the type, which is a finite tree, so `conforms` is total by the structural rule of ADR 0035 and unfolds into a fixed formula. For a recursive `t` (ADR 0047), the recursive arm recurses on a sub-value of `v` as well, so it is total by structural recursion on the document, which is a finite datatype value.

Three functions use it, generated per type by `@derive(json)` and called through the concept:

```ocaml
let check (t : type) (v : borrowed json) : bool
  requires valid_dom v
  ensures result <==> conforms t v

let from_dom (t : type) (v : borrowed json) : or_oom t   (* t, or result t oom if t allocates *)
  requires valid_dom v && conforms t v

let to_dom (t : type) (x : t) (a : ...) : result json oom
  ensures (match result with | Ok v -> valid_dom v && conforms t v | Err _ -> true)
```

- **`from_dom` cannot fail on shape.** Its precondition is the conformance, so the only error left is `OutOfMemory`, and only if `t` holds a `string` or a `vec`. Its result type is the type-level metaprogram `or_oom t`, which is `result t oom` for such a `t` and plain `t` otherwise, so for most types there is no error path to handle at all. A program proves `conforms` either by calling `check` and branching on it, or by having built the document with `to_dom`, or from any other fact that implies it:

```ocaml
let get_point (v : borrowed json) : option point
  requires valid_dom v
= if Json.check point v then Some (Json.from_dom point v) else None
```

- **The three paths agree**, as a law of the concept: reading `t` from text gives `Ok v` exactly when parsing the text gives a document `d` that conforms to `t` and `from_dom t d = v`. So a program may stream, or parse once and convert several times, and get the same values and the same accepted inputs either way.
- **Branded documents come later.** Once refinements on values work ([status.md](../status.md)), `conforming t` will be a type, `{ v : json where valid_dom v && conforms t v }`, so the proof travels with the value across function and module boundaries instead of as a `requires` on each function. Until then the precondition form is the same proof with more writing.

### 7. Streaming input, depth and speed

- **The lexer is a state machine**, stated with the prelude's `machine` theory ([theories.md](../theories.md#state-machines)), and keeps no state outside its record. So it can stop at the end of one chunk and resume with the next, which is what streaming from a file or socket needs. The first version works over a complete slice; chunked input arrives with `Pia.Io`'s `reader` concept, and a pull reader as a coroutine with [ADR 0027](0027-coroutines-and-race-freedom.md).
- **Depth.** Derived readers of non-recursive types need no depth limit (section 2). Readers of recursive types and `Json.Dom.parse` take a maximum depth as a range-typed argument, so their stack use is proved.
- **SIMD.** The first lexer is scalar. A structural-character scanner in the style of simdjson's first stage comes with `vec<T, k>` (M10), proved against the same `Json.Spec`, so nothing above the lexer changes.

### 8. What this ADR does not decide

- Floating-point numbers wait for floats (M11), as Dean decided. Until then numbers read into integer and range types, exactly, and a DOM keeps every number as its literal. `f32` and `f64` fields then need a correctly rounded decimal conversion proved against real arithmetic ([ADR 0038](0038-float-kernels-against-real-theories.md)), which is its own piece of work.
- JSON Schema import and export. A metaprogram could generate a schema from a type, or a type from a schema, but neither is needed here.
- Other formats. The derive is JSON-specific. A serde-style format-independent data model can be factored out once a second format (CBOR, MessagePack, the PNG chunk readers of M13) exists to test it against.

## Gaps this depends on

These are listed, not worked around:

| Gap | What waits on it |
| --- | --- |
| `str` and `Pia.Core.Utf8` (C++23 library thread, phase 1) | every string token, and the lexer's UTF-8 proof |
| `string` and `vec` storing its allocator (`Pia.Mem` and Vec thread, #86, #72) | `string` and `vec t` fields, the DOM's arrays and objects |
| Metaprogram builtins `attrs`, `variants`, `int_bounds` and string bytes in metaprograms ([stdlib.md](../stdlib.md), section 11) | `@json(...)` attributes, variant codecs, fused range checks, key decision trees |
| Generic types and concepts in interfaces ([ADR 0039](0039-module-and-interface-syntax.md) step 3, in progress) | importing `Json` from `lib/Pia/Text/Json` into other modules |
| Core tuples (own ADR, per ADR 0040 section 9) | tuple codecs and mixed-kind arrays |
| Value refinements (`where` on values) | branded `conforming t` documents (section 6) |
| Lifetime markers on results ([ADR 0042](0042-lifetimes-liveness-and-escape-analysis.md)) | zero-copy `str` fields, and a DOM borrowed from its input |
| Recursive sum types ([ADR 0047](0047-recursive-sum-types-and-shared-references.md)) | the DOM (sections 5 and 6), and `@derive(json)` on user types that contain themselves |
| Floats (M11) | float fields (section 8) |
| `Pia.Io` readers and writers | chunked streaming from files and sockets |
| `vec<T, k>` (M10) | the SIMD scanner |

The order below starts with what needs none of them.

## Implementation order

1. **`Json.Spec` and `Json.Lex` over `[u8]`**: tokens, positions, escapes and UTF-8 validation (with a minimal local UTF-8 spec if `Pia.Core.Utf8` has not landed), proved memory safe, terminating and accepting exactly the token grammar.
2. **`Json.Write`** into a caller's `out [u8]` with a proved capacity, then into `vec u8`; escaping and integer formatting proved against `Json.Spec`.
3. **The metaprogram builtins** the derive needs (`attrs`, `variants`, `int_bounds`, string bytes).
4. **`@derive(json)` for records of integers, bools and fixed arrays**: readers with key decision trees, seen-field sets, fused range checks and exact error sets; writers; `Json.read t`.
5. **Variants (structural disambiguation and tags), `option`, `vec`, `str` and `string`**, then tuples once core tuples land.
6. **`Json.Dom`**, once ADR 0047's recursive variants work: the `json` type, `valid_dom`, `parse` with a bounded depth, on-demand unescaping. Built (`lib/Pia/Text/Json/Dom.pia`) with these differences from section 5: a number or string is the `span` of its token, not a slice, since a recursive value does not yet hold borrowed slices of its input; `null` is `JNull`, since `Null` is the lexer's token kind; an array's `vec` and an object's are fixed-length, each counted before it is read and taken in one allocation from one of two bumps the caller lends, one of values and one of members; and `valid_dom` is `@opaque` (ADR 0063), revealed one constructor at a time, since unfolded in the parser's loops it cost a hundred times the goals. Unique keys and on-demand unescaping are not built yet.
7. **`Json.Shape`**: `conforms`, `check`, `from_dom` and `to_dom`, per type, and recursive user types. Built for records of integers, range types and bools (`lib/Pia/Text/Json/Shape.pia`), as a companion derive, `@derive(json, json_dom)`, so that `@derive(json)` alone needs no DOM: `conforms_json_<t>` (exactly one member per field, each in its field's range or a bool, no other member), `check_json_<t>`, which decides it, `from_dom_json_<t>`, with no failure path and each field its member's value, and `to_dom_json_<t>`, which writes the value with `@derive(json)`'s writer, parses it back and checks it, so its document is valid and conforms. An integer conforms when it has only digits after an optional minus, with no fraction or exponent, as for the streaming reader. Not yet: that to_dom's text always parses and conforms (a lemma relating the writer's digits, `Spec.magnitude`, to Shape's), option, array and nested record fields, variants and recursive user types.
8. **The laws**: `round_trip`, and agreement between streaming and DOM paths, proved per derived type from per-field lemmas, with `proof_bench` watching their cost.
9. **A literate page, `docs/json.pia.md`**, with every example doc-tested, and the C++ map updated (`nlohmann::json` and Boost.JSON have no `std` header, so it gets a row under "beyond the standard").
10. **Chunked streaming** over `Pia.Io`, and the SIMD scanner with M10.

## Consequences

- JSON is the first full use of derives beyond `eq`, so it exercises the metaprogram builtins, error-set unions, type-level metaprograms, concepts with laws and allocators together. Gaps it hits are fixed in the core, not in the library.
- A program that reads JSON into a type gets, from the type alone, a reader that cannot index out of bounds, cannot accept malformed or non-UTF-8 input, returns only fully initialised values that meet the type's refinements, and reports exactly the errors that type can produce.
- Strict defaults (unknown and duplicate members rejected) mean some real-world documents need `@json(ignore_unknown)`. That is the intended trade: the relaxation is visible in the type's source.
- The DOM waits on recursive sum types, a core feature (ADR 0047). The streaming codecs do not, so they come first.
- Untagged variants make some types need a tag where serde would silently use the constructor's name. That is the intended trade: the encoding is always what the type's source says.
- Proof cost grows with the number of derived types and their fields, linearly by construction. Derived proofs go in the benchmark corpus from step 4.

## Dean's answers (2026-11-22)

1. **DOM.** Backed by the raw input as slices, and built with recursive types, not a tape. Dean wants algebraic sum types to support recursion explicitly, and, once there is a box type, a reference and a weak reference type that use a concept for recursive types. Section 5 now uses `let rec`; the core work is [ADR 0047](0047-recursive-sum-types-and-shared-references.md).
2. **Names.** Only field names appear in the output, or the key a tag on the field gives, as in serde and Go. Variants are told apart by structure and type, or by a tag member that is also written explicitly. Section 2 now proves untagged variants disjoint and makes a tag the explicit alternative; there is no external tagging.
3. **Strictness.** Yes: unknown and duplicate members are rejected by default.
4. **Numbers.** Wait for floats: float fields arrive with M11, and there is no interim float representation beyond the DOM's literal text.
