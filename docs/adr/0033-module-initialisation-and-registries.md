# 33. Module initialisation: registries, proved `@init` hooks, and opt-in dynamic registration

Date: 2026-11-21

Status: Proposed

## Context

[ADR 0024](0024-published-proof-certificates.md) keeps Pia images free of dyld-run static initializers, so the certificate check always runs before any guarded code. Dean accepted it on condition that Pia gets a supported hook and a standardised registration mechanism for initialisation. In C++ that is implementation-defined; in Pia it must be well-defined and proved in advance. He added that at dynamic load time a library should call a runtime-provided function that registers its initialisers, much like the REPL ([ADR 0031](0031-verified-repl-and-live-environment.md)) but without a JIT: newly loaded symbols and functions are registered with the runtime and can be looked up, including through an `eval`-like mechanism.

C++ static initialization has an unspecified cross-unit order, lets one initializer read another's unconstructed object, lets initializers throw, loop or start threads, and runs them inside the loader. Ada's elaboration checks, Go's dependency-ordered `init`, Rust's refusal of life-before-main, and linker sets are the main alternatives. The full design is in [docs/init.md](../init.md).

## Decision

- **Registries for registration without code.** `let r : registry t where P` declares one; `@register(M.r) let e = ...` adds a compile-time constant entry, proved against `t` where it is defined. The linker collects entries into a constant table ordered by module name then entry name. Whole-set properties such as `unique (.name)` are checked by the static linker and again by the loader when libraries add entries.
- **One `@init` per module, for state that must be built at run time.** It returns the module state's initial value and establishes its invariant; its signature and contract are in the interface hash. It must be proved to terminate, is infallible unless it declares an error set (which is then in the interface), gets only the capabilities in `init_env` (root allocator, arguments, environment, clock), and cannot spawn, await or lock. Teardown is the state's `Drop`, which cannot fail.
- **A proved order.** Every function that reads module `M`'s state has an implicit precondition `initialised M`. Inits run in a topological order of the init dependency graph (an edge where an init reads another module's state, which must be an import), with ties broken by module name. Reading state that is not yet initialised is a verification error, and a cycle is a compile or link error. Dependency sets go in the certificate, so the order is computed from certificates alone.
- **The runtime runs inits, never dyld.** Images carry `__TEXT,__pia_init` and `__DATA_CONST,__pia_reg` tables and no `__mod_init_func`. At launch, the Pia entry point runs the certificate check, the registry checks, the inits in order, `main`, then the drops in reverse. A failed init drops what already ran, and `main` never runs.
- **Opt-in dynamic registration, `Pia.Dyn`, on the REPL's environment model without a JIT.** Each image has one compiler-generated registration function, `_pia$register$<image>`, which `Pia.Dyn.open` calls after the certificate check. It hands the runtime constant tables of symbols (name, interface hash, pointer, eval adapter), registry entries and inits. The runtime rejects name clashes, checks registries, runs the new inits in order, and undoes everything on failure. `Pia.Rt` does not contain `Pia.Dyn`, just as it does not contain `Pia.Live`.
- **Typed lookups.** `Pia.Dyn.bind env I lib` returns a record typed by interface `I` only if the library registered `I`'s hash, or a version proved to refine it. `find` and `bind_symbol<t>` do the same for one symbol. So a lookup never returns a value whose contract differs from its certificate.
- **`eval` on `dyn` values.** `Pia.Dyn.eval env name args` checks argument tags against the registered type, and checks the function's `requires` at run time with a compiled checker (the eval adapter), because no proof covered the call. Results satisfy the `ensures`. Only exports marked `@eval` get adapters, and the certificate lists them.

## Implementation

Issues: registries and `@register` ([#100](https://github.com/deanberris/pia-lang/issues/100)); `@init`, `initialised M` and the init order ([#101](https://github.com/deanberris/pia-lang/issues/101)); `__pia_init`/`__pia_reg` and the launch sequence in `Pia.Rt` ([#102](https://github.com/deanberris/pia-lang/issues/102)); `Pia.Dyn` with registration functions, `open` and `close` ([#103](https://github.com/deanberris/pia-lang/issues/103)); typed `bind`, `find` and `eval` with eval adapters ([#104](https://github.com/deanberris/pia-lang/issues/104)).

## Consequences

- Initialisation order is a pure function of the program's modules, and the order fiasco becomes a proof goal with a counterexample.
- Most static-initializer uses need no run-time code at all: registries are constant data.
- Pia images still run nothing at dyld load, so ADR 0024's soundness argument holds.
- Programs that never load code dynamically carry none of `Pia.Dyn`.
- The REPL and dynamic loading share one environment representation and one notion of compatible change.
- `eval` trades proofs for run-time precondition checks, visibly, and only where a module opts in.
