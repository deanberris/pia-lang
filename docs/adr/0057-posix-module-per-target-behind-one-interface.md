# 57. `Pia.Sys.Posix` is one generated module per target behind one hand-written interface, and the generator joins the contract overlay

Date: 2026-11-23

Status: Proposed

## Context

[ADR 0051](0051-variadic-generics-and-foreign-varargs.md), section 6, generates Pia's POSIX declarations from each target's headers and puts the contracts in a hand-written overlay. A `posix` metaprogram was to join each overlay row with its generated signature. Steps 1 and 2 are built:

- `@variadic(n)` foreign calls (PR #308);
- `tools/bindings/gen.py`, which writes `lib/Pia/Sys/Gen/<target>.pia`, and a CI job that regenerates it on each platform (PR #322).

The generated files are per target, and every item in them is `@target(m)`. Building step 3 shows three gaps in the plan:

- **A metaprogram cannot do the join.** `listing ()` sees only the items of the module it runs in ([meta.md](../meta.md)), and a module is one file ([ADR 0039](0039-module-and-interface-syntax.md), section 1). An overlay that is shared between targets cannot sit in the same file as two per-target generated files.
- **Target-generic code cannot call `@target` items.** Only `@target` code of the same model can call them, or the `then` branch of an `if Target.is m` ([ADR 0049](0049-targets-are-theories.md)). `Pia.Sys.Fs` and `Pia.Io` are written once for both targets. Wrapping every call in a per-target dispatch would double the library.
- **Constants would leak into proofs.** ADR 0049 says that OS constants come from the target's model, so a target-generic proof sees only what holds on every target. A literal `let o_creat : i32 = 64` in scope would let a proof rely on Linux's value.

## Decision

### 1. One module, one interface, one file per target

Each target's generated file is the module `Pia.Sys.Posix` for that target. The build picks the file by target, as `select` already picks per-target flags (`tools/piac/targets.bzl`). The module meets one interface, `Posix`, which is written by hand in `lib/Pia/Sys/Posix.pia`:

```ocaml
interface Posix = sig
  (** read(2): reads at most n bytes, and writes no more than it returns. *)
  let read : (fd : i32) -> (buf : out mutable [u8]) -> (n : usize) -> isize
    requires n <= len buf
    ensures result >= -1 && result <= n
  let o_creat : i32
  let eagain : i32
end
```

- **The interface is the overlay.** Each `let` in it is one row of the overlay. A row holds the Pia modifiers of each parameter, the contract with its manual page, and any `@blocking` or variadic condition. Importers see only the interface, as for any module ([ADR 0039](0039-module-and-interface-syntax.md)).
- **Constants are opaque.** `let o_creat : i32` in the interface has no value, so importers' proofs cannot depend on 64 or 512. Inside the module the value is known, and codegen links the constant per target. This is ADR 0049's rule (constants come from the target's model), reached through the module system instead of a new theory.
- **Target-only names are `@target` rows.** Examples are `epoll_wait`, `eventfd`, `kevent` and `so_nosigpipe`. Per ADR 0049, section 3, they appear only in their own target's interface. `Pia.Io`'s io_uring and kqueue models reach them from `@target` code, which ADR 0050 already plans.

### 2. The generator joins the overlay, and fails on any mismatch

`tools/bindings/gen.py` reads `lib/Pia/Sys/Posix.pia` together with the headers. For every row of the interface, it writes the contracted declaration into the generated module:

```ocaml
let read (fd : i32) (buf : out mutable [u8]) (n : usize) : isize
  requires n <= len buf
  ensures result >= -1 && result <= n
= extern "read"
```

It fails if any row does not fit the header:

- the row names a symbol or constant the target's header lacks;
- a parameter's Pia type is not the C type's width and signedness;
- a parameter marked `mutable` or `out` is a `const` pointer in C;
- the row is not variadic where C's function is, or the other way around.

Each of these is something a metaprogram could not see, because it knows only Pia types. The join runs when the file is generated, and the drift check runs it again on each platform in CI. So a header change that breaks a row is a red build on that platform. `piac` also proves that the module meets `Posix`, since the module and its interface are compiled as any other ([ADR 0039](0039-module-and-interface-syntax.md), section 4).

### 3. Symbols without a row stay out of the interface

The generated module still declares every symbol listed in `posix.toml`, without a contract, so the generator can check it. A symbol with no row in the interface is private to the module. So `unsafe` calls to uncontracted POSIX functions are not possible outside `Pia.Sys.Posix`. To use a symbol, give it a row. This is stricter than ADR 0051, which allowed `unsafe` calls to any generated declaration, and it keeps the trusted surface to the rows that have been read against a manual page.

### 4. The `posix` metaprogram is not built

The join is done by the generator, so the metaprogram planned in ADR 0051, section 6, is dropped. `bit_family` and other stamping metaprograms are unaffected.

## Implementation steps

1. `lib/Pia/Sys/Posix.pia` with the `Posix` interface, first for the rows `Pia.Sys.Fs` needs (`open`, `close`, `read`, `write`, `pread`, `pwrite`, `lseek`, `fsync`, `fstat`, `unlink`, the `O_` and `SEEK_` constants and the errno values).
2. `gen.py` reads the interface, checks each row against the header, and writes `module Pia.Sys.Posix : Posix` with the contracted declarations. Its `@target` attributes go, since the build picks the file.
3. A `pia_library` per target, selected by platform, and a test that each file meets the interface on its own target (`tests/std`).
4. Then `Pia.Sys.Fs` (#57) on top, written once for both targets.

## Consequences

- `Pia.Sys.Fs`, `Pia.Io` and the rest of the library are target-generic, and call `Posix.read` without dispatch.
- Proofs above `Pia.Sys.Posix` cannot depend on a platform's constant values, which ADR 0049 requires.
- The trusted surface is the interface file, one row per symbol, each citing its manual page. The trust report lists the rows.
- The header checks are done in Python, at generation, rather than in a metaprogram. They are stronger, since they see C's `const` and its exact types, but they run only when the file is regenerated, which CI does on every pull request.

## Question for Dean

1. **Where should the overlay be joined?** The recommendation is the generator (section 2): it can check C's `const`-ness and exact types, and a metaprogram cannot see across the per-target files. The alternative is to keep the metaprogram planned in ADR 0051. That needs both targets' declarations in one file under distinct names, every row stamped twice, and a dispatch through `if Target.is` in every target-generic caller.
