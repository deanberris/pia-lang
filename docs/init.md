# Module initialisation and registries

Status: proposed, 2026-11-21. Decision record: [ADR 0033](adr/0033-module-initialisation-and-registries.md). Builds on [ADR 0024](adr/0024-published-proof-certificates.md) (certificates and the loader), [ADR 0006](adr/0006-contracts-and-module-state.md) (module state), [ADR 0028](adr/0028-error-propagation-and-cleanup.md) (errors and cleanup) and [ADR 0026](adr/0026-memory-manager.md) (allocators), and follows the REPL's environment model ([ADR 0031](adr/0031-verified-repl-and-live-environment.md)).

Programs need code that runs before `main`: tables to build, codecs to register, caches to allocate. C++ does this with static initializers, and almost everything about them is implementation-defined. The order across translation units is unspecified (the "static initialization order fiasco"), an initializer can read another one's object before it is constructed, it can throw, loop forever or start threads, and the platform runs it from inside the dynamic loader, before any program code can check anything.

Pia supports the same uses through one supported hook and one registration mechanism, both **well-defined and proved in advance**:

| Need | C++ | Pia |
| --- | --- | --- |
| A table of things that other modules add to (codecs, commands, tests, plugins) | A global object whose constructor registers itself | A **registry**: declarative entries collected at link time. No code runs |
| State that must be computed at run time (allocate a cache, read the environment) | A static initializer | One **`@init` function** per module, run by the Pia runtime in a proved order |
| Teardown | Static destructors, in reverse of an order nobody knows | The module state's `Drop`, in exact reverse init order |

Anything that can be computed at compile time still is: module-level `let` values are constants, folded by the compiler ([ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md)), and need neither mechanism.

## Registries: registration without code

A module declares a registry, with the type and refinement every entry must meet. Any module that imports it can add entries, which must be compile-time constants (records, function values, strings):

```text
\ image.pia
let codecs : registry codec
  where unique (.name)                  \ no two entries share a name

\ png.pia, which imports Image
@register(Image.codecs)
let png = { name = "png"; magic = "\x89PNG"; decode = Png.decode; encode = Png.encode }
```

- **No code runs.** `piac link` collects every entry for a registry into a constant table in the image. Reading a registry is reading a constant slice.
- **Deterministic order.** Entries are ordered by the registering module's fully qualified name, then by the entry's name. The order never depends on link order, file order or load order.
- **Proved entries.** Each entry is proved against the registry's element type and refinement where it is defined, like any other value. A registry's contents are therefore known to meet the refinement, and proofs about a registry quantify over its entries (`forall c in Image.codecs. ...`).
- **Cross-entry properties are checked when the set is known.** A property over the whole set, such as `unique (.name)`, cannot be proved by any one module. The static linker checks it when it builds the table, and the loader checks it again whenever `Pia.Dyn.open` adds entries (below). A duplicate is a link error, or an `Err (RegistryConflict ...)` from `Pia.Dyn.open`, never a silent override.
- **Dynamic libraries add entries.** Each image carries its entries in a `__DATA_CONST,__pia_reg` section (read-only after fixups, so code signing covers it). `Pia.Rt.entries Image.codecs` returns a borrowed snapshot of the entries from every loaded image. `Pia.Dyn.close` cannot run while a snapshot is borrowed, by the ordinary borrow rules, so no entry can disappear under a reader.

Registries cover most of what static initializers are used for, with nothing to order and nothing that can fail.

## `@init`: the run-time hook

When a module's state genuinely has to be built at run time, the module declares one initialiser:

```text
\ glyphs.pia
let cache : state glyph_cache                       \ module state, ADR 0006

@init
let setup (env : borrowed Pia.Rt.init_env) : glyph_cache
  ensures valid result
  = Glyph_cache.create env.alloc 256
```

The rules, all checked by `piac`:

1. **One `@init` per module, and only in the module that owns the state.** It returns the initial value of the module's state symbol, and its `ensures` must establish the state's invariant. Its signature and contract are part of the module's interface, so they are in the interface hash.
2. **Proved to terminate.** Loops need `decreases` measures and recursion needs a variant, as for any total function. There is no "loops until something else is ready".
3. **Infallible by default.** An `@init` has no error set unless it declares one, so the strongest guarantee is the default ([ADR 0004](adr/0004-strongest-guarantee-by-default.md)). A fallible init declares its error set, `: result glyph_cache (OutOfMemory)`, which becomes part of the interface, and the loader handles failure as described below. It can never fail in a way nobody handles.
4. **Explicit capabilities.** An init gets only what `init_env` gives it: the root allocator, the program arguments and environment, and a clock. It can call `extern` functions only through `@trusted` modules, as everywhere else. It cannot spawn tasks that outlive it, await, or take locks, so inits run sequentially and never deadlock.
5. **It may read only what is already initialised.** An init may read the state of a module only if that module is one of its imports. Every function that reads module `M`'s state carries an implicit precondition `initialised M`, which the verifier discharges from the init order below. Calling such a function from an init that does not depend on `M` is a verification error with the call chain as the counterexample. This is what rules out the order fiasco: the problem becomes a proof goal.
6. **Teardown is the state's `Drop`.** If the state type has a `Drop` instance, it runs at exit (or `Pia.Dyn.close`) in exact reverse init order. Cleanup cannot fail ([ADR 0028](adr/0028-error-propagation-and-cleanup.md)), so teardown cannot fail either.

### The order

Imports are explicit and form a DAG ([ADR 0010](adr/0010-modules-interfaces-and-proof-certificates.md)). The init order is a topological order of the **init dependency graph**: an edge from `N` to `M` whenever `N`'s init (or anything it calls) reads `M`'s state. Ties are broken by fully qualified module name, so the order is a pure function of the program's modules, the same on every run and every machine. A cycle in the init graph is a compile error (or a link error, when it spans modules compiled separately) that names the cycle.

The compiler computes each init's dependency set and records it in the certificate. The order for a whole program is then computed from certificates alone, at link time for static links and at load time for `Pia.Dyn.open`, without looking at code. `pia-cert audit` recomputes the dependency sets from the embedded proof bundle and checks that the certificate's claims are right.

## Dynamic registration: `Pia.Dyn`

Loading code at run time works like the REPL ([ADR 0031](adr/0031-verified-repl-and-live-environment.md), [repl.md](repl.md)) without the JIT. The REPL keeps an environment of verified definitions, each with its interface hash. `Pia.Dyn` keeps the same kind of environment, filled by loading compiled, certified libraries instead of compiling cells. Like `Pia.Live`, it is **opt-in**: `Pia.Rt` does not contain it, and a program has none of its machinery unless it imports `Pia.Dyn`.

```text
let env = Pia.Dyn.create root_alloc                  \ an empty environment, owned by the caller
let lib = Pia.Dyn.open env "libpng_codec.dylib" ?   \ check, register, run inits
let png = Pia.Dyn.bind env Codec.Interface lib ?    \ typed record of Codec's functions
let img = png.decode bytes ?
Pia.Dyn.close env lib
```

### The registration hook

A Pia library does not register itself when dyld loads it. Instead `piac` generates one **registration function** per image, `_pia$register$<image>`, which is the image's only entry point for the runtime. `Pia.Dyn.open` calls it after the certificate check, passing a runtime handle, and the function calls back into the runtime:

```text
register_symbols  handle  [ (qualified name, interface hash, symbol pointer, eval adapter) ... ]
register_entries  handle  [ (registry, entry) ... ]
register_inits    handle  [ (module, init function, dependency set, drop function) ... ]
```

Every argument is a constant table that the compiler builds from the module's exports, `@register` entries and `@init` functions. The registration function itself contains no user code, so it trivially terminates and cannot fail. The runtime, not the library, decides what to do with what was registered: it checks that no qualified name is already in the environment, checks registry constraints, computes the init order, and runs the inits. The same tables are also emitted as data (`__TEXT,__pia_init` and `__DATA_CONST,__pia_reg`), so `pia-cert` and the static linker can read them without running anything, and the audit checks that the function and the tables agree.

A library loaded by a C host goes through the same path, with `pia_rt_open` as the C face of `Pia.Dyn.open`.

### Typed lookup

The main way to use a loaded library is to **bind an interface**:

```text
Pia.Dyn.bind env Codec.Interface lib : result (Codec.Interface.record) (Missing | Mismatch)
```

The caller names, at compile time, an interface it imports, so it was proved against that interface's contracts. `bind` compares the interface hash in the caller's certificate with the hashes the library registered (including older versions it proves it refines, [abi.md](abi.md#abi-evolution)). On a match it returns a record of function values typed by that interface. Calls through it are ordinary calls whose contracts the caller already proved, so no run-time contract checking is needed. On a mismatch it returns `Err`, never a value with the wrong contract. A lookup can never return a function whose contract differs from what its certificate says, because the hash compared is the certificate's.

`Pia.Dyn.find env "Png.decode" : option (symbol)` looks up a single name and returns its qualified name, type and interface hash. `Pia.Dyn.bind_symbol<t>` turns it into a value of type `t` under the same hash check, for callers that need one function instead of a whole interface.

### `eval`

For code that does not know the type at compile time (a command console, a scripting bridge, the REPL calling into a loaded library), `Pia.Dyn.eval env name args` calls a registered function on `dyn` arguments ([ADR 0003](adr/0003-static-typing-with-tagged-dyn.md)):

- The arguments' tags are checked against the function's registered type, so a wrong type is `Err (TypeMismatch ...)`, never undefined behaviour.
- The function's `requires` cannot have been proved by the caller, so it is checked at run time. For every exported function that may be `eval`ed, `piac` compiles its `requires` into a checker, the same code `@check` produces, and registers it as the **eval adapter**. A failed check is `Err (PreconditionFailed ...)` and the function does not run.
- The result comes back as a `dyn` whose `ensures` holds, because the function was proved to meet it.
- Whether a function can be `eval`ed is its module's choice (`@eval` on the export, or on the module), so libraries that never want dynamic calls carry no adapters. Adapters are listed in the certificate, so the trust report shows which preconditions are checked at run time instead of proved.

This is the same split as the REPL: proved, typed calls are the default, and the dynamic path is safe because it checks exactly what a proof would otherwise have covered.

### Consistency with the REPL

| | REPL session ([ADR 0031](adr/0031-verified-repl-and-live-environment.md)) | `Pia.Dyn` environment |
| --- | --- | --- |
| Holds | Verified definitions with interface hashes | Loaded symbols with interface hashes from certificates |
| Adds definitions by | Compiling and verifying a cell, then JIT | Loading a certified library, then its registration function |
| Initialisation | Cells run in order | `@init`s run in the proved init order |
| Name clash | Error; `:redef` replaces with re-verification | Error; close the old library first. Live replacement is `Pia.Live`'s job |
| Lookup | By name inside the session | `bind` by interface hash, `find`, `eval` |
| Opt-in | `Pia.Live` | `Pia.Dyn` |

The two share one environment representation, so the REPL can load a compiled library into a session through `Pia.Dyn`, and its cells can then call the library's functions with full proofs, or `eval` them.

## Loader integration

Pia images still run **no code when dyld loads them**. That keeps the soundness argument of [docs/abi.md](abi.md#layer-2-the-certificate-check): the certificate check always runs before any code it guards. Inits are run by the Pia runtime, after the check, from a table instead of `__mod_init_func`:

```text
__TEXT,__pia_init   per module: module name, init function, state symbol,
                    declared error set, init dependency set (module names
                    and interface hashes), drop function or none
```

The certificate records the same per-module facts (has init, error set, dependency set), and the init's contract is part of the interface hash, so an importer proved against "state initialised with this invariant" cannot bind to a library whose init no longer establishes it.

**At launch**, a Pia program's entry point (in `Pia.Sys.Process`, see [stdlib.md](stdlib.md)) does, in order:

1. the certificate check for every loaded Pia image (Layer 2 in [abi.md](abi.md));
2. registry cross-entry checks;
3. every `@init` in the global order;
4. `main`;
5. state drops in reverse order, then `exit`.

If a fallible init fails, the inits already run are dropped in reverse order, `main` never runs, and the program exits with a fixed status and a message naming the module and the error. There is no implicit initialisation path: a program that never imports `Pia.Dyn` initialises only the images it was linked against, at launch.

**On `Pia.Dyn.open`**, the runtime checks the new images' certificates, calls their registration functions, computes the init order of the modules that are not initialised yet (modules shared with images already loaded keep their state), checks the new registry entries against the existing ones, and runs the new inits. If any step fails, it drops the new modules' state in reverse order, closes the images, removes their registry entries and returns `Err (InitFailed { module, error })` or `Err (RegistryConflict ...)`. The program's state is exactly what it was before the call.

**On `Pia.Dyn.close`**, the closed images' state is dropped in reverse init order. A module that other loaded images still depend on stays loaded, as dyld already does for its dependencies.

## What this replaces in abi.md

[docs/abi.md](abi.md) said that Pia images have no static initializers. That is still true at the dyld level: no `__mod_init_func`, and the certificate check still rejects a Pia image that has one. What changes is that module initialisation now exists, as `@init` and registries run by `Pia.Rt` after the check.

## Prior art

- **C++** static initialization and the order fiasco; `[[gnu::init_priority]]` and function-local statics as workarounds. Pia makes the order a property of the import graph, and reading uninitialised state a proof failure.
- **Ada elaboration**: `pragma Elaborate_All`, `Preelaborate`, `Pure`, and GNAT's static elaboration model, which checks at compile time that no unit is used before it is elaborated. This is the closest relative. Pia's `initialised M` precondition is the same check, made a proof goal.
- **Go** package `init` functions run in dependency order, but can fail only by panicking and can do arbitrary work.
- **Rust** has no life-before-main by design. Lazy statics and `ctor` crates exist outside the language.
- **Linker sets** (FreeBSD `SET_DECLARE`, ELF and Mach-O custom sections collected by the linker): Pia's registries are linker sets with types, refinements and a deterministic order.
- **Swift** global variables are lazily initialised on first access with `swift_once`. Pia rejects lazy init because it hides the order and adds a check on every access.

## Implementation plan

Issues are listed in [ADR 0033](adr/0033-module-initialisation-and-registries.md#implementation).
