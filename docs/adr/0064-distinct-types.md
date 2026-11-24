# 64. `type` always makes a new type: `let length = type u32` is distinct from `u32`, converts only through named functions, and inherits only what it derives

Date: 2026-11-24

Status: Proposed. Dean asked for strong type aliases (2026-11-24), and chose the spelling in section 1, `type` always makes a new type, over a separate `distinct` word (2026-11-24).

## Context

Reading [the tour](../tour.md), Dean asked for strong type aliases: after `let length = type u32`, a `length` is a type of its own, never mixed up with a `u32` or with another type over `u32`, and every conversion is an explicit function call. He suggested a metaprogram could make the conversion functions.

Today `let byte = type u8` is another name for `u8` ([irgen.md](../irgen.md#types)): types are structural, so `u64` and `usize` are one type and `int{0..255}` is `u8`. Records and variants are the exception. They are named, so two records with the same fields are different types. The language has no way to give a scalar, a range or an existing record a name that the type checker keeps apart, so a function `area (w : u32) (h : u32)` cannot stop a caller swapping its arguments, and a `u32` of pixels can be added to a `u32` of bytes.

The questions to settle are how it is spelled, whether the underlying type's bounds and contracts carry over, which operators and concepts the new type gets, how it meets types as values, concepts, error sets, `@derive(json)` and the ABI, and what it costs at run time and in proofs.

## Decision

### 1. `type` makes a new type; a `let` of a type names one

```ocaml
let length = type u32              (* a new type, distinct from u32 *)
let percent = type int{0..100}     (* a new type over a range *)
let byte = u8                      (* another name for u8, as before *)
```

`type` already makes a new type when it is followed by a record or a variant. This ADR makes that the whole rule: `type e` is a new type whose values are the values of `e`, whatever `e` is. Since types are values ([ADR 0002](0002-single-let-binding-form.md)), naming an existing type needs no keyword at all: `let byte = u8` binds the type `u8` to a second name, as `let y = x` binds a value. That is how a transparent alias is spelled from now on.

No keyword is added. The existing aliases spelled with `type` (about ten of them in `tests`, `docs/theories.md` and ADR 0051's example, such as `let blk = type int{0..63}`) become `let blk = int{0..63}` in the same change that flips the meaning, so their programs do not change. `max byte` and `min byte` keep working for an alias ([ADR 0059](0059-digit-separators-and-type-bounds.md)).

On the right of `let`, a type expression with no `type` is an alias: a type name, a range `int{lo..hi}` (written with no space before `{`, by the adjacency rule of [ADR 0019](0019-grammar-disambiguation.md)), an applied generic such as `option u8`, or a type-level metaprogram's call ([ADR 0035](0035-substitution-failure-and-total-constraints.md)). Sema tells it apart from a value binding because it names a type.

### 2. It is built by a prelude metaprogram

The expander rewrites `let n = type e`, where `e` is not a record or variant literal, into a call of the prelude metaprogram `distinct`, which returns:

```ocaml
let length = type { raw#length : u32 } @distinct
let to_length (x : u32) : length ensures from_length result = x = { raw#length = x }
let from_length (x : length) : u32 ensures result = x.raw#length = x.raw#length
```

- **A one-field record.** Records are already nominal through Sema, IRGen, generics, interfaces and certificates, so a distinct type reuses all of it. The field's name carries a `#`, which no source name can, so the only ways in and out are the two functions; no program can write `l.raw`.
- **`to_n` and `from_n`.** The names follow the library's `to_chars` and `from_chars`: `to_length` makes a `length`, `from_length` takes one apart. They are ordinary functions, so they can be passed as values, and a module may leave them out of its interface to keep the type's values under its own control (section 6).
- **`@distinct`** marks the record so that the rest of the compiler can tell a distinct type from a hand-written one-field record: diagnostics print `length (distinct u32)`, derives write the underlying value (section 4), and the metaprogram builtin `underlying t` returns `e` for a distinct type and unit for any other.

`distinct` is ordinary Pia in `src/syntax/Prelude.cpp`, like `derive_eq` and `machine`, and a program can call it itself.

### 3. Bounds and contracts carry over; conversions are explicit both ways

- **Bounds.** The field has the underlying type, so a `percent` holds 0 to 100 and the prover knows it about every `percent`, for free, as for the range itself. `to_percent x` has the narrowing goal `x` fits `int{0..100}` at its argument, as any call does, and `from_percent p` returns an `int{0..100}`, which widens implicitly to anything larger.
- **Contracts.** `from_length` is a pure function of scalars, so in a contract it means its body ([tests/verify/pure_calls.pia](../../tests/verify/pure_calls.pia)), and `requires from_length w * from_length h <= max u32` reads and proves as the scalar version did.
- **No implicit conversion, in either direction.** `let l : length = 5` is an error that suggests `to_length 5`, a `u32` where a `length` is expected is an error that suggests `to_length`, and a `length` where a `u32` is expected suggests `from_length`. Two distinct types over one type never convert into each other except through both functions.
- **`min` and `max`.** `max length` is an error that suggests `to_length (max u32)`: the bounds are values of the underlying type, and folding them to a bare literal would be the implicit conversion this ADR rules out. `@derive(bounds)` (section 4) gives `min_length` and `max_length` as values of `length`.

### 4. Nothing is inherited; operators come from derives

A distinct type starts with no operators, no equality in code, and meets no concept. This is the point of it: a `length` that could be added to itself could also be multiplied by itself, and length times length is an area. Each family is opted into with a derive, which writes ordinary overloads on the record:

| Derive | Gives | Meaning |
| --- | --- | --- |
| `eq` | `=`, `<>` | the existing `derive_eq`: compares the underlying values |
| `ord` | `<`, `<=`, `>`, `>=` | compares the underlying values, each with a postcondition that says so |
| `add` | `+`, `-` between two values of the type | results of the type; overflow is a goal as for the underlying type (ADR 0004) |
| `scale` | `*`, `/`, `%` by the underlying type, on the right | `length * u32 : length`, never `length * length` |
| `bounds` | `min_n`, `max_n` | the underlying type's bounds, as values of the type |
| `hash` | an instance of `Pia.Core.Hash` | the underlying value's hash; needs `eq` |
| `json` | `write_json_n`, `read_json_n` and the `Json` instance | the underlying value, not an object: a `length` is the JSON number `5`, read with the underlying type's range check |

```ocaml
let length = type u32 @derive(eq, ord, add, scale)
```

A derive's postconditions are written in terms of `from_n`, so callers prove facts about `a + b` the way they would about the underlying numbers. Concepts follow from the functions: a concept whose signature `ord` meets is met by any distinct type that derives it, and an adapter ([ADR 0009](0009-generics-concepts-adapters.md)) covers anything else. A program can write any operator itself, such as `let mul (a : length) (b : length) : area`, which is how units are built ([theories.md](../theories.md), "Units").

`@derive(add)` on a distinct type over a type with no `add`, such as a record, is an error at the derive, which names the missing function.

### 5. Types as values, generics, error sets

- **Types as values.** `length` is a type value like any record: `option length`, `[length; 8]`, `vec length` and a generic's `(t : type)` all take it. A generic over `(t : type where Ord t)` accepts `length` when it derives `ord`.
- **Over records and variants.** `let celsius = type reading` is a distinct type over the record `reading`. It does not copy `reading`'s fields or constructors (constructors are one namespace, and copies would clash); it wraps one `reading`, reached through `from_celsius`.
- **Error sets.** An error set's members are variants ([ADR 0028](0028-error-propagation-and-cleanup.md)), so a distinct type is not one, even over a variant. A handler matches the variant itself. Making a distinct type over a variant usable as an error set member is left until someone needs it.
- **Distinct of distinct.** `let width = type length` wraps a `length`; `to_width` takes a `length`, not a `u32`.

### 6. Interfaces, certificates and abstract types

- **Interfaces.** An interface shows a distinct type as it is defined, `let length = type u32`, and exports the functions it chooses. The `.piai` carries the `@distinct` record, so importers agree on its layout, and the interface hash covers the type's name and its underlying type: changing `u32` to `u64` changes the hash and the importers' witnesses ([ADR 0024](0024-published-proof-certificates.md)).
- **Abstract types.** An interface that lists `let length : type` and exports `to_length` but not `from_length`, or a checked constructor in its place, keeps the type's values under the module's control. This is what makes a distinct type with an invariant possible (a `sorted` slice, a `nonzero` divisor). Abstract types are not importable yet ([ADR 0039](0039-module-and-interface-syntax.md)); this ADR does not change that, and invariant-carrying distinct types are a later ADR.

### 7. Zero cost

- **Proofs.** `transforms::scalarizeRecords` replaces each record with its fields before the verifier runs ([irgen.md](../irgen.md#records)), so a proof about a `length` is the proof about a `u32`, with the same goals and cost. Conversions are calls of pure scalar functions, which the verifier unfolds.
- **Code.** After scalarization a `length` is a `u32`: a buffer of `length` is one buffer of `u32`, and the conversions inline away.
- **The C ABI.** A record parameter is already passed as its fields. A record result is written through an out-pointer today ([codegen.md](../codegen.md)); this ADR makes a record of one scalar field return that scalar instead. That is what C does for a `struct { uint32_t v; }` on arm64 and on x86_64 System V, so the entry point is the same as for the underlying type, and also what a C caller expects for a one-field struct.

### Alternatives

- **A `distinct` word, keeping `type u32` as an alias** (`let length = distinct u32`). Additive, with nothing to migrate, but it adds a word for something `type` already means for records and variants, and leaves two spellings of "name a type" (`type u8` and `u8`). Dean chose `type` instead (2026-11-24).
- **A core nominal type in Sema and the dialect** (`!pia.distinct<"length", ui32>`). Every pass that compares types would learn a new case, and the verifier and codegen would need to strip it, for the same result the record gives already.
- **One-constructor variants** (`type | Length of u32`). Nominal today, but a variant carries a tag, matching is the only way out, and a derive would have to treat one-constructor variants specially.
- **Inheriting everything the underlying type has.** Rejected: it re-admits `length * length : length`, which is the class of bug the feature exists to stop. Haskell's `GeneralizedNewtypeDeriving` and Rust's newtype pattern both make derivation explicit for this reason.
- **Implicit conversion from literals.** `let l : length = 5` would be pleasant, but it is a conversion the reader cannot see, and it makes `to_length` optional in exactly the places (constants, defaults) where units are most often wrong.

## Consequences

Implementation, one PR each:

1. **Aliases spelled `let byte = u8`.** Sema accepts a `let` whose right side is a type expression as an alias, `type <scalar>` keeps meaning an alias for now, and every existing `type`-spelled alias in the repository moves to the new spelling. Tests: `tests/verify/type_aliases.pia`, `tests/irgen/alias_errors.pia`.
2. **`type e` is distinct.** The prelude's `distinct`, the `@distinct` attribute, the `underlying` builtin, the diagnostics that suggest `to_n` and `from_n`, and one-scalar-field records returned as the scalar in the C ABI. Tests: `tests/verify/distinct_types.pia`, `tests/irgen/distinct_errors.pia`, `tests/codegen/distinct_abi.pia`, `tests/meta/distinct.pia`.
3. **Derives.** `ord`, `add`, `scale` and `bounds` in the prelude, and `eq` checked on distinct types. Tests: `tests/verify/distinct_derives.pia`.
4. **`json` and `hash`.** `derive_json` and `Pia.Core.Hash` write and hash the underlying value. Tests in `tests/std`.

Docs: the tour's Records section and `docs/irgen.md` (types), `docs/meta.md` (`distinct`, `underlying`, the new derives), `docs/grammar.md` (aliases), and the pia-language skill. ADR 0059's `let byte = type u8` example becomes `let byte = u8`.

Open questions:

1. The conversion names. `to_length`/`from_length` match the library; the alternative is to make a type callable, `length 5`, with an overloaded `raw l` out. That reads well but makes a type a function, which nothing else does.
2. Whether `@derive(add)` should also give `+|` and `-|` (saturating) when the underlying type has them. Proposed: yes, as one family.
