# 39. Modules are private by default: one module per file, interfaces list every export, imports name interfaces

Date: 2026-11-22

Status: Accepted (Dean, 2026-11-22), with the answers recorded under "Review"

## Context

Dean asked how a function is kept private in a module. [ADR 0010](0010-modules-interfaces-and-proof-certificates.md) answers in principle: a module exports named interfaces, and an importer names each interface it uses, so a module depends on interface artifacts only. [docs/design.md](../design.md#modules-interfaces-and-imports) sketches the syntax (`interface X = sig ... end`, `module M : X = struct ... end`, `import M.X`), and the grammar already parses it. None of it is built. Today `piac` compiles one program from one or more files, and every top-level function gets a C entry point ([codegen.md](../codegen.md#limits-of-v0)), so nothing is private.

Since ADR 0010, many decisions have added things an interface must carry or a module must own:

- contracts, refinement types and module state as exported symbols ([ADR 0006](0006-contracts-and-module-state.md));
- metaprograms and operators, found by module-qualified names and argument-dependent lookup (ADL) ([ADR 0022](0022-metaprogram-hygiene.md));
- the interface hash, the inline surface hash, witness symbols and certificates ([ADR 0024](0024-published-proof-certificates.md)), and layout hashes ([ADR 0030](0030-published-object-layouts.md));
- `@suspends`, `@blocking`, `@acquires`, `@protocol` and `sendable`/`shareable` ([ADR 0027](0027-coroutines-and-race-freedom.md));
- error sets in `result` types ([ADR 0028](0028-error-propagation-and-cleanup.md));
- `@init`, `initialised M` and registries ([ADR 0033](0033-module-initialisation-and-registries.md));
- concepts, adapters and overloads ([ADR 0034](0034-concepts-and-overload-resolution.md)), and type-level metaprograms ([ADR 0035](0035-substitution-failure-and-total-constraints.md));
- theories and `import M trusting` ([ADR 0036](0036-library-theories.md));
- the REPL's session environment ([ADR 0031](0031-verified-repl-and-live-environment.md)) and the language server ([ADR 0021](0021-language-server.md)).

Build time is a tracked benchmark ([ADR 0032](0032-parallel-sliced-cached-proving.md)). The module system is where most of it is won or lost: a change that cannot affect an importer must not make the importer rebuild.

Prior art. OCaml has one module per file, with an optional `.mli` that seals it. Anything not in the `.mli` is private, and `open` brings every name into scope. Standard ML and OCaml signatures can hide a type's representation (`type t`) or show it (`type t = ...`). Haskell export lists and Rust's `pub` mark exports at the definition. Rust adds `pub(crate)` for exports within a crate. Ada and Modula-3 split a specification from its body, and both are compiled separately. Go has one package per directory, exports by capital letter, and compiles against export data only. C++ modules (`export module M;`) have interface units whose compiled form (BMI) importers read. Dafny's `export` sets and `reveals`/`provides` say, per export, whether importers see a definition or only its signature. F\* `.fsti` files seal a module and are checked against it. Bazel's Java rules build against interface jars (`ijar`), so a change to a method body does not rebuild dependents. That is the property Pia wants, with contracts in the interface.

## Decision

### 1. A file is one module, named by a header

The first item of a file may be a module header:

```ocaml
module Pixels : PixelOps, PixelCodec
```

The header names the module and lists the interfaces it claims. The rest of the file is the module's body, so the body is not indented and needs no `= struct ... end`. Module names are dotted paths of capitalised segments, such as `Pia.Sys.Posix` or `Image.Png`. The name comes from the header, not from the file's path, and the build checks that no two modules share a name. `Pia.*` is reserved for the standard library.

Attributes on the module go after its name: `module Pia.Sys.Posix @trusted : PosixCalls`.

`module M : I = struct ... end` keeps its meaning as a nested module inside a file. A nested module is a namespace (`M.f`) sealed by `I`: the file's other code sees only what `I` lists. A nested module is private to its file, and cannot be exported in this version. It is useful for checking that an implementation meets an interface, and for keeping helpers apart. Adapters already use `struct ... end` ([ADR 0034](0034-concepts-and-overload-resolution.md)).

### 2. Everything is private unless an interface lists it

A top-level `let` in a module is private unless an interface the module claims lists its name. That covers functions, types, values, state, spec functions, lemmas, metaprograms, operators, concepts, adapters, theories and registries. A private item:

- is still proved, like any other item;
- gets internal linkage in LLVM and no C entry point, so it can be inlined, specialised and removed when unused;
- is not hashed into any interface, so changing it, adding it or removing it never makes an importer re-prove, recompile or relink.

There is no `pub`, `export` or `private` keyword. The interface is the export list, which keeps one place that says what a module promises, and makes adding an export a visible change to an interface.

An interface is declared in the module that claims it, as today:

```ocaml
module Pixels : PixelOps, PixelCodec

interface PixelOps = sig
  let pixel : type                                  (* abstract: importers cannot see the fields *)
  let spec alpha : (p : pixel) -> u8                 (* opaque spec function: name and type only *)
  let opaque : pixel
  let blend : (a : pixel) -> (b : pixel) -> (t : u8) -> pixel
    ensures alpha result = max (alpha a) (alpha b)
end

interface PixelCodec = sig
  let encode : borrowed in [pixel] -> [u8]
  let decode : borrowed in [u8] -> result [pixel] decode_error
  let decode_error = type | Truncated | BadHeader    (* transparent: importers can match on it *)
end

let pixel = type { r : u8; g : u8; b : u8; a : u8 }
let opaque : pixel = { r = 0; g = 0; b = 0; a = 255 }
let spec alpha (p : pixel) : u8 = p.a
let mix (x : u8) (y : u8) (t : u8) : u8 = ...        (* private: in no interface *)
let blend (a : pixel) (b : pixel) (t : u8) : pixel = ...
...
```

An interface is an ordinary item and must also follow the no-shadowing rule. Its name is the last segment of an import path, so a module cannot have an interface and a nested module with the same name.

### 3. `:` hides, `=` shows

An interface item written with `:` gives importers a name, a type and a contract. An item written with `=` also gives them the definition. This one rule covers every kind of item:

| Item in a `sig` | Importers see | Changing the definition costs importers |
| --- | --- | --- |
| `let t : type` | an abstract type, with its shape hash only ([ADR 0030](0030-published-object-layouts.md)) | nothing, unless the shape changes (relink) |
| `let t = type ...` | the representation: fields, variants, refinements | re-prove, as it changes the interface hash |
| `let f : (x : a) -> b requires ... ensures ...` | a function's type and contract | nothing |
| `let inline f : ... = body` | the body as well, for inlining | recompile, through the inline surface hash |
| `let n : u32{1..8192}` | a fixed value's type and refinement; the value is folded at link time ([ADR 0010](0010-modules-interfaces-and-proof-certificates.md)) | recompile, through the inline surface hash |
| `let n : u32 = 4096` | the value itself, which proofs may use | re-prove |
| `let spec s : ...` | an opaque spec function, known only through contracts and exported lemmas | nothing |
| `let spec s : ... = body` | a transparent spec function, which proofs may unfold | re-prove |
| `let lemma l ...` | the lemma's statement; its proof stays in the module | nothing |
| `let meta m ...`, `let meta operator ...` | the metaprogram, which importers run | re-prove, since its expansion is their code |

So the representation of a value is hidden unless the author chooses to show it, and showing it is the choice that couples importers to it. Two kinds of change do not need the importer to be re-proved but do need it to be recompiled: a changed inline body and a changed foldable value. They are hashed separately into the inline surface hash ([ADR 0024](0024-published-proof-certificates.md)), so the build re-runs codegen but reuses proofs.

Generic functions follow the same split. An exported generic function is checked once against its constraints in its own module (the definition check of [ADR 0034](0034-concepts-and-overload-resolution.md)), and importers instantiate it. Its body goes into the inline surface, as instances need it for codegen. Its signature and constraints are in the interface hash.

Everything an exported contract mentions must itself be visible to importers. A `requires` that calls a private spec function, or an `ensures` that names a private type, is an error that names the item to export. This is what lets an interface compile on its own.

### 4. A module meets its interfaces by proof

For each item an interface lists, the module must define an item with that name and:

- **the same type**, including parameter modifiers, refinements and the error set of a `result`. An implementation that raises fewer errors still declares the interface's set;
- **a contract at least as strong**: the interface's `requires` implies the definition's, and the definition's `ensures` implies the interface's. This is the requirement check of [ADR 0034](0034-concepts-and-overload-resolution.md), reused, so an interface can promise less than the body proves and keep the rest private. It is proved by the solver, and the result is cached like any goal;
- **compatible effects**: `@suspends` and `@blocking` must match exactly, because they change the calling convention. The definition's `@acquires` levels must be a subset of the listed ones, and its inferred `@protocol` must refine the listed protocol ([ADR 0027](0027-coroutines-and-race-freedom.md)). Exported types list `sendable` and `shareable` when importers may rely on them, and the module must prove them;
- **for an abstract type**, any type at all, with the interface's refinement, if it has one, proved as its invariant.

An item an interface lists that the module does not define is an error, and so is a module that claims an interface twice. Several interfaces may list the same item. An interface is hashed on its own, so each importer depends only on the interfaces it imports, even when they share items.

### 5. Imports name interfaces, and access is qualified

```ocaml
import Pixels.PixelOps                       (* Pixels.blend, Pixels.pixel *)
import Image.Png.Codec as Png                (* Png.decode *)
import Pia.Task.Tasks { scope, spawn, join } (* scope, spawn and join unqualified; the rest Pia.Task.* *)
import Pia.Nn.Spectral.Bounds trusting       (* required because the interface has trusted axioms *)
```

- An import names one interface of one module, by its full path. Its items are then reachable as `Module.name`. The interface name is not part of the item's name, since an item belongs to the module and may be listed in several interfaces. Naming an item of a module that is in an interface this module does not import is an error that says which interface to import.
- `as` gives the module a shorter local name. `{ a, b }` also brings the listed names in unqualified. Both are checked against the no-shadowing rule ([ADR 0022](0022-metaprogram-hygiene.md)), so a clash is reported at the import.
- There is no wildcard, like OCaml's `open`, and no import of a whole module. A library may add items to an interface as a compatible change (it refines its old baseline, [ADR 0024](0024-published-proof-certificates.md)). With a wildcard, a new item could clash with a name in an importer, and a compatible update would break its build.
- `trusting` is the opt-in of [ADR 0036](0036-library-theories.md): it is required when the imported interface, or an interface it depends on, has trusted axioms, and the error without it lists them.
- An import is a fact the build checks. Each import must be provided by a declared dependency (strict dependencies), and an import that nothing uses is a lint warning ([ADR 0037](0037-idiomatic-pia-and-lints.md)).
- An interface can mention types from interfaces its module imports. Its hash then includes theirs, and an importer's build reads those artifacts too, to type check. The importer still cannot name their items without importing them.

### 6. Names reach across modules only through imports

[ADR 0022](0022-metaprogram-hygiene.md) and [ADR 0034](0034-concepts-and-overload-resolution.md) defined lookup for operators, derives, concept requirements and adapters in terms of "the type's module plus imported modules". With modules, that becomes:

- **ADL searches the interfaces this module imports** from the type's own module, and the adapter interfaces it imports explicitly. A type reached without importing its module, for example the result type of another library's function, has no operators or concept functions in scope. The error says which interface to import. This keeps every name a module can use inside the interfaces it names, which is what makes the build graph explicit.
- **An operator or derive for a type is exported with the type**: an interface that lists `let meta operator ( + ) for vec<t, k>` must also list `vec`, or import the interface that does.
- **Quotes produce module-qualified paths.** A free name in a quote refers to its definition in the metaprogram's module (`Pixels.mix`, `prelude.add`). If that name is private, the expansion in an importer can still call it: the quoted path is resolved by the defining module, which links it as a hidden symbol that only expansions of its own exported metaprograms may reference. The `[prelude]` and `[toplevel]` marks of ADR 0022 go away.
- **Concept satisfaction is checked where it is used**, against the functions and adapters visible there, as now. Its proof (requirement contracts implied) is cached by the interface hashes involved, so two importers that check `Eq pixel` share one proof.

### 7. Module state is a symbol, and importers cannot write it

Module state is a top-level `let` whose type is `mutable`, with an `invariant`, as in the REPL today (docs/repl.md, "State"):

```ocaml
module Counter : Counting

interface Counting = sig
  let count : fixed u32                    (* importers may read it, never write it *)
  invariant count <= 100                   (* importers may assume this between calls *)
  let bump : () -> unit
    ensures count = min 100 (old count + 1)
end

let count : mutable u32 invariant count <= 100 = 0
let bump () : unit = if count < 100 then count <- count + 1 else ()
```

- State is private by default, like everything else. An interface may export it only as `fixed`, a read-only view. Writes go through exported functions, whose `ensures` (with `old`) say how the state changes. So the module alone keeps its invariant, and importers reason only through contracts ([ADR 0006](0006-contracts-and-module-state.md)).
- An interface may publish the state's `invariant`, or a weaker one. Every exported function must preserve the published invariant, and importers may assume it between calls. Private state can be described to importers through an exported opaque spec function, `let spec level : () -> u32`, so an interface can talk about state without exposing it.
- A function that reads the module's state has the implicit precondition `initialised Counter` ([ADR 0033](0033-module-initialisation-and-registries.md)). For exported functions it is part of the canonical interface, so `piac --emit=interface` prints it and importers' `@init`s are checked against it. `@init` itself is never listed in an interface, since nobody calls it, but its contract, error set and dependency set are hashed into the module's certificate, as ADR 0033 decided.
- Registries are items like any other. `let r : registry t where P` is exported by listing it, and `@register(M.r)` needs an import of the interface that lists `r`.

### 8. Interfaces compile on their own

`piac --emit=interface pixels.pia` parses the file, runs metaprogram expansion to its fixed point, type checks the interfaces and the items they list, and writes one artifact per interface (`Pixels.PixelOps.piai`). It does not check bodies or run the verifier. An interface artifact holds the canonical serialisation of [ADR 0024](0024-published-proof-certificates.md), and its SHA-256 is the interface hash. The inline surface is a second artifact with its own hash. Both must be byte-for-byte reproducible: no paths, no timestamps, and hygiene scope ids taken from the expansion site, as ADR 0022 required.

The Bazel rule `pia_library` builds one module. Importers depend only on its `.piai` artifacts, never on its object file or certificate, so:

- a change to a private item, or to a body behind `:`, leaves the `.piai` artifacts byte-identical, and Bazel's action cache skips every importer;
- every module that imports an interface can type check and verify as soon as that interface is extracted, which is fast, so module proofs run in parallel across the whole build, on top of the per-goal parallelism of ADR 0032;
- the linker checks the certificates, and `pia_binary` names the root module, whose `main` is the program's entry point. `main` is never listed in an interface.

### 9. C entry points come from interfaces

Only exported functions get external symbols. Their names are mangled from the module path (`_pia$Pixels$blend`, with overloads named as in [ADR 0034](0034-concepts-and-overload-resolution.md)). An interface marked `@abi(c)` gives its functions plain C names instead (`blend`), checked for clashes at link time, and must keep to types with a C calling convention ([codegen.md](../codegen.md)). That is how a C harness, such as `//tests/codegen:saturate_test`, calls Pia code. The `@abi(c)` mark is in the interface hash.

### 10. A file without a header is a program with nothing exported

A file with no module header is an anonymous program module. All of its items are private, and only `main` (if any) is an entry point. Every item is still proved, so `piac --verify` and the documentation examples, which only verify, behave as before. Tests that call Pia from C get a module header and an `@abi(c)` interface. This keeps the strongest guarantee as the default ([ADR 0004](0004-strongest-guarantee-by-default.md)): no file exports anything by accident. Several headerless files given to one `piac` command still form one program module, as now.

### 11. Internal interfaces

An interface marked `@within(Pia.Sys)` can be imported only by modules whose names start with `Pia.Sys`. This is for interfaces that a library shares between its own modules but does not promise to users, such as `Pia.Sys.Posix`'s raw calls, which only the rest of `Pia.Sys` should reach. It is an import rule, not a hiding rule: the interface is hashed, certified and checked like any other.

### 12. The REPL

- A REPL session is an anonymous module, as a headerless file is. Every cell's items are visible to later cells, and nothing is exported.
- `import M.I` in a cell loads the interface artifact and the library that provides it through `Pia.Dyn` ([ADR 0033](0033-module-initialisation-and-registries.md)), so a cell sees exactly what a compiled importer would.
- `pia repl --module pixels.pia` opens a session *inside* a module: its private items are visible and can be redefined, which is how private helpers are explored and debugged. A redefinition must still meet every interface the module claims, which is the compatible-change rule of [ADR 0031](0031-verified-repl-and-live-environment.md). A redefinition that would change an interface hash is refused with the importers it would affect, unless `:redef` is given `--change-interface`. The MCP server's `execute` takes the same commands.

### 13. The language server

- `pia-lsp` keeps an index of the workspace's interfaces, built with `piac --emit=interface`, which is front-end work and fast enough to run on every save. Imports, completion, hover and go-to-definition use the index, so they work across files without proofs.
- Hover on an imported name shows the interface's contract, which is what the importer may rely on. Inside the module it also shows the definition's contract, when it is stronger.
- Diagnostics: a use of a name that is private to another module, with the interface that would need to list it; a name in an interface the file does not import, with a code action that adds the import; an unused import. A code action that adds an item to an interface warns that it changes the interface hash, and how many workspace modules import the interface.
- Proof diagnostics stay per file, but an edit that changes no interface artifact no longer invalidates other files' proofs.

## Implementation

In steps, each a PR with tests, as for ADR 0034:

1. **Headers and privacy in one compilation.** Parse the header, check interfaces as items, the matching rules of section 4, privacy (internal linkage, no C entry point), `@abi(c)`, and headerless files as program modules. Migrate the tests that call Pia from C.
2. **Interface artifacts and separate compilation.** `--emit=interface`, the canonical form and hashes, `import M.I` resolved through `--iface-path`, assume-guarantee verification against imported contracts, and the `pia_library` and `pia_binary` Bazel rules with strict dependencies.
3. **Names across modules.** Qualified access, `as` and `{ ... }`, cross-module ADL for operators, derives, concepts and adapters, exported metaprograms and qualified quotes.
4. **The inline surface.** `let inline`, foldable values with link-time folding, and exported generic bodies.
5. **State, effects and initialisation.** `fixed` state views, published invariants, implicit `initialised M`, and effect and protocol matching. This joins [#101](https://github.com/deanberris/pia-lang/issues/101).
6. **Certificates and trust.** Required interfaces and their hashes in the certificate, witness symbols, `trusting` and `@within`.
7. **REPL and language server.** `import` in cells, `pia repl --module`, and the workspace interface index in `pia-lsp`.

Step 3 is landing in the order the standard library ([ADR 0040](0040-cpp23-standard-library-in-pia.md)) needs it: shown types first, then concepts and generic functions, spec functions in signatures, postconditions of `out` and `inout` functions, and then `as`, `{ ... }` and cross-module ADL.

- **Shown types.** An interface shows a type with `=`, including a generic one as it is defined: `let option = let (t : type) => type | None | Some of t`. An importer names it through its module, `Pia.Core.Option.option u8`, and gets the same definition, so the two modules agree on its layout. The constructors of an imported variant are in scope unqualified, as `Some`, and also as `Pia.Core.Option.Some`. Constructors are already one namespace in a program, so a clash between two imported variants, or with a local one, is an error at the type, as for any two constructors. Abstract types (`let t : type`) are not importable yet, since an importer needs their layout ([ADR 0030](0030-published-object-layouts.md)).

## Consequences

- A function is private unless an interface lists it. Privacy costs nothing to write, and exporting is a deliberate change to one place.
- Changing a private item, or a body behind `:`, never rebuilds an importer, which is the main lever on build time for large programs.
- Interfaces can promise less than a module proves, so a module can strengthen its body's contracts freely without coupling importers to them.
- Qualified names are longer to write than OCaml's `open`. `{ ... }` and `as` cover the common cases, and the language server adds imports.
- A type's operators and concept functions are only usable by a module that imports the type's interface. Some programs need one more import line.
- Single-file programs keep working, but nothing in them is callable from C until they gain a header.
- Nested modules cannot be exported yet. Re-exporting another module's items from an interface (a façade such as `Pia.Io` over `Pia.Sys.Fs`) is left for later, and so is choosing between implementations of one interface at link time (like OCaml functors or Backpack).

## Review

Dean accepted this ADR on 2026-11-22 and answered its questions:

1. **A headerless file exports nothing** (section 10). Accepted.
2. **Access is qualified unless an import lists names in `{ ... }`, with no wildcard** (section 5). Accepted.
3. **Importers can never write module state** (section 7). Accepted: state changes go through interface functions, which is safer. Exporting `mutable` state needs a demonstrated case before it is considered again.
4. **Spellings `@abi(c)` and `@within(...)`** (sections 9 and 11). Accepted.
