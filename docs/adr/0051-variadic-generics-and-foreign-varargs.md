# 51. Variadic functions and types take a pack that is called like any argument list, walked by metaprograms and proved once; foreign bindings are generated from tables

Date: 2026-11-23

Status: Proposed (revised twice on 2026-11-23 after Dean's reviews: plain call syntax, metaprograms instead of recursive `match`, foreign bindings generated from headers, partial application through the expected type, `...` for packs, and sums over a pack matched by type)

## Context

Dean (2026-11-23): "we need the equivalent of variadic functions that are provably safe. We should have language features for generic variadic functions and types, like C++ gives us, but with more straightforward syntax through metaprograms."

Three things need variadics now:

- **C functions.** `open`, `fcntl`, `ioctl` and `syscall` are C variadic functions. [ADR 0050](0050-senders-and-receivers.md) needs `syscall` for io_uring, and `Pia.Sys.Fs` needs `open` with a mode. Apple arm64 passes variadic arguments on the stack, while named arguments go in registers, so declaring `open` with a fixed third parameter gives the wrong ABI. x86_64 System V also needs `%al` set to the number of vector registers a variadic call uses. Pia's FFI today takes only fixed integer, bool and buffer parameters (`genForeign`).
- **Generic code over any number of types.** `when_all (a, b, c)` in ADR 0050 completes with the values of all its senders and the union of their error sets. `format` takes any number of arguments of types that meet `Format`. `apply`, `tuple_cat`, `std::get` by type and argument forwarding for constructors are the same shape.
- **Types over any number of types.** An operation state for `when_all` holds one child per sender, and `std::variant<Ts...>` is a sum over a list of types.

C++ answers with parameter packs: `typename... Ts`, pack expansions `f(xs)...` in a dozen syntactic positions, fold expressions `(... + xs)`, `sizeof...`, and recursion through partial specialisation or `if constexpr`. They are powerful, but the syntax is irregular. Pack indexing only arrived in C++26, and an error inside an expansion surfaces at instantiation. C varargs (`va_list`) are unchecked: the callee trusts the caller's count and types, which is the root of format-string bugs.

[ADR 0040](0040-cpp23-standard-library-in-pia.md), section 9, already decided that tuples are a core type and that tuple types are the type lists for variadic code, "without a separate pack feature", and said core tuples need their own ADR. This is that ADR. It also covers the parts section 9 left open: how generic code walks a tuple and is proved, variadic types, and foreign varargs.

## Decision

### 1. Core tuples

This section builds what ADR 0040 section 9 specifies, unchanged:

- `(a, b, c)` is a tuple value, and `(u8, str, bool)` is its type, since types are values. `()` is `unit`. There is no one-element tuple.
- `t.0`, `t.1`: positional access, checked at compile time.
- A tuple is an anonymous record with fields `0`, `1`, ... It has the same layout, ownership, `moved`, `@linear`, borrow and contract rules as a record, and struct-of-arrays buffers. Two tuple types with the same element types are the same type.
- `Eq`, `Ord` and `Hash` are structural, proved once (ADR 0043).


### 2. A variadic function is called like any other function

The last parameter of a function may be a **pack**, written `...`, with its type a deduced type parameter:

```ocaml
(* Designed syntax. *)
let print (ts : type where All Format ts) (w : borrowed inout writer) (xs : ...ts) : unit = ...

print w x name 42u8              (* ts = (u32, str, u8), deduced *)
print w                          (* ts = (), an empty pack *)
```

- **The call site is ordinary application.** A pack takes every argument that follows the fixed ones in that application. An application ends where it always ends: at a closing parenthesis, an operator, `;`, `then`, `in` and so on. So `print w x name 42u8` is one call with three pack arguments, and `print w (f x) y` is one call with two. Nothing about the call says the function is variadic.
- **Inside the body, the pack is a tuple.** `xs` has the tuple type `ts`. Its elements are `xs.0`, `xs.1` and so on, or `xs.[u8]` by type, which is the one element of type `u8` and a type error when there is not exactly one (C++'s `std::get<T>`; types are values, so a type is an index like any other). The pack can be passed on whole, so ADR 0040's tuple decision still holds: a pack is a tuple, and only the parameter is marked.
- **Passing a tuple as a pack** is `...t` at the call: `print w ...pair`. This is how one variadic function forwards its pack to another, as C++'s `f(xs...)` does.
- **Partial application goes through the expected type.** When a variadic call is in a place that expects a function, such as an argument whose parameter type is `u32 -> unit`, the call is partial, and the expected function's parameters close the pack. So `map (print w) xs` passes `print w` as a function of one argument, with `ts` deduced as `(t)` from `map`'s parameter, and `for_each (print w prefix) xs` fixes the first element too. When nothing expects a function, the call is complete, and `print w` prints nothing. This is the same deduction from the expected type that generic results already use ([docs/irgen.md](../irgen.md)).
- **Variadic function values.** `bind_front print w` keeps the pack open: it is a function object whose `apply` is itself variadic, so a later call can pass any number of arguments. `Pia.Fn` has the usual combinators over packs: `bind_front`, `bind_back`, `compose`, `flip`, `apply` (a function and a tuple, as `std::apply`) and `unpack` (a function of a tuple, turned into a variadic one). The `Function` concept ([ADR 0044](0044-function-values-and-lambdas.md)) takes a pack of argument types, `Function f (...args) r`, so higher-order functions can accept variadic function values and be proved once over them.
- **`All c ts`** is a prelude concept over pack types: every element type meets `c`. Concepts are already values that type-level metaprograms take ([ADR 0046](0046-box-over-a-type-or-a-concept.md)).

### 3. Packs are walked by metaprograms, not by recursion

Code never recurses over a pack. Two kinds of metaprogram do the walking instead.

**Type-level metaprograms over a list of types.** The builtin `elements ts` gives a pack type's element types as a metaprogram list, and `tuple_of xs` builds a pack type from a list. Everything else is the list functions metaprograms already have, `map`, `fold` and `length` ([docs/meta.md](../meta.md#the-interpreter)):

```ocaml
let meta size (ts : type) : usize = length (elements ts)

(* when_all's value and error types (ADR 0050). *)
let meta values_of (ss : type) : type = tuple_of (map value_of (elements ss))
let meta errors_of (ss : type) : type = fold (let (a) (e) => a | e) never (map error_of (elements ss))
```

These are total by the rule tactics already follow ([docs/meta.md](../meta.md#tactics)): the only recursion is `map` and `fold` over the components of a parameter.

**A loop over a pack, unrolled by expansion.** In code, a `for` over a pack runs its body once for each element, and the expansion stamps out one copy of the body per element, as Zig's `inline for` does. `x` has each element's own type in its copy:

```ocaml
let print (ts : type where All Format ts) (w : borrowed inout writer) (xs : ...ts) : unit
  ensures written_count w = old (written_count w) + size ts
= for i, x in xs
    invariant written_count w = old (written_count w) + i
  do format w x done
```

The library's `Pia.Core.Pack` is written the same way: `map`, `fold`, `apply`, `cat`, `get` by type and `zip`. C++'s fold expressions become `fold`, `sizeof...` becomes `size`, and pack indexing becomes `xs.i` with a constant `i`, or `xs.[t]` by type.

### 4. Proved once, though compiled per element

The loop above is proved once, as an ordinary loop. Its body is proved for an abstract position `i` and an abstract element type `element i ts`, which is an abstract sort constrained only by `Format`, because `All Format ts` says that much of every element ([ADR 0043](0043-generic-definitions-proved-once.md)). The invariant is the induction over positions, exactly as for `for i in 0 .. n`. Each unrolled copy is then discharged by that one proof, as an instance of a generic is.

So a variadic function is proved and checked once, at its definition, for every pack, and errors are reported there rather than at an instantiation (ADR 0034's definition check). That closes C++'s gap, where a pack expansion fails only when instantiated. Codegen still compiles straight-line code: `print w a b c` becomes three calls of `format`, with no loop and no run-time dispatch.

### 5. Variadic types

A generic type's last type parameter may be a pack too, and an instance is written like any other generic application, `when_all_sender a b c`. Its fields use type-level metaprograms over the pack:

```ocaml
(* when_all's operation state: one child operation per sender (ADR 0050). *)
let when_all_op (r : type) (ss : ...type where All Sender ss) = type {
  children : tuple_of (map (let (s) => op_of s (child_receiver r)) (elements ss));
  results  : tuple_of (map (let (s) => option (value_of s)) (elements ss));
  rcv      : r;
}
```

**A sum over a pack** is `one_of ts`, C++'s `std::variant<Ts...>`: a value that holds exactly one element of the pack, and knows which. It is a core anonymous sum, with no constructor names, because types are values and the type of the active element is enough to tell the alternatives apart:

```ocaml
let reading = type one_of u32 str (option u8)

let describe (w : borrowed inout writer) (r : reading) : unit =
  match r with
  | (n : u32) -> format w n
  | (s : str) -> format w s
  | (o : option u8) -> format_opt w o

let r : reading = 42u32                      (* injected: the expected type is a one_of *)

(* Generic over the alternatives: one arm, proved once for an abstract element. *)
let show (ts : type where All Format ts) (w : borrowed inout writer) (v : one_of ...ts) : unit =
  match v with
  | x -> format w x
```

- **`match` on the active element's type** is how a `one_of` is read. Arms are type patterns, and the `match` must cover every element type, or end in an arm that binds the rest generically. That one generic arm is `visit`, with no library function needed.
- **Element types must be distinct**, which `one_of` checks with a type-level `distinct ts`, so a type always names exactly one alternative. A variant whose alternatives share a type, such as two `u32`s that mean different things, is a named variant (`type | Celsius of u32 | Kelvin of u32`), which says what each one means.
- **`v.[u32]`** is the element when it is a `u32`, with the precondition `holds v u32`, a spec function that a `match` arm or an `if holds v u32` establishes. `index v` is the position of the active type in the pack.
- **Layout** is a tag and the largest element, as for named variants, and `Eq`, `Ord` and `Hash` come from the elements, as for tuples.

### 6. Foreign bindings: variadic C calls, and declarations generated from tables

**A C variadic function is declared once, with a pack.** A pack in a foreign declaration is restricted to C-promoted types, and each call passes whatever its arguments are, with the ABI emitted for that call:

```ocaml
(* open(2): the mode is read only when O_CREAT or O_TMPFILE is set. *)
let open (ts : type where All CPromoted ts) (path : cstr) (flags : i32) (mode : ...ts) : i32
  requires (flags & o_creat <> 0) = (size ts = 1)
  requires size ts = 1 ==> element 0 ts = u32
  ensures result >= -1
= extern "open"

open path o_rdonly                         (* 2 arguments *)
open path (o_creat | o_wronly) 420u32      (* 3 arguments; 420 is 0644 *)
```

- **Calls use the variadic ABI.** Codegen emits each call as a variadic LLVM call with the argument types of that call, so Apple arm64 puts the pack on the stack and x86_64 sets `%al`.
- **`CPromoted`** holds for `i32`, `u32`, `i64`, `u64`, `isize`, `usize`, buffers (passed as pointers) and, once floats land, `f64`. A narrower integer or a `bool` fails the constraint with a message that says to widen it, because C would promote it and the callee would read an `int`. A record fails it, because C cannot pass a struct through `...` portably.
- **The contract decides what a call may pass.** What the C function reads depends on its other arguments, as `open` reads a mode only with `O_CREAT`. So the declaration's `requires` relates the pack's size and element types (`size ts`, `element i ts`) and values (`mode.0`) to the other arguments, and every call proves it. This is the "provably safe" part: the `va_arg` reads that C trusts become goals.
- **`cstr`** is a `[u8]` refined to end in a NUL byte, which `Pia.Sys` builds and proves. It is not a new core type.
- **Pia functions are never C-variadic.** Pia's own variadic functions take packs, which are tuples, and nothing in Pia makes or reads a `va_list`. Exporting a variadic function to C is not supported.
- **Format strings stay in Pia.** `printf` and its family are not declared. `Pia.Text.Format` uses section 2, with `requires placeholders fmt = size ts`, which the verifier folds when `fmt` is a literal. So a format string with the wrong number of arguments is a failed goal, not a crash.

**Declarations are generated from the platform's headers, with contracts beside them.** POSIX alone needs a few hundred declarations, most of them per target, so `Pia.Sys.Posix` writes none of them by hand. Writing them as tables by hand would drift from the platforms, so they are generated:

- **A generator reads the headers.** `tools/bindings` runs the pinned clang on a list of headers for one target (`<fcntl.h>`, `<sys/socket.h>`, `<linux/io_uring.h>` and so on), with `-ast-dump=json`, and writes `lib/Pia/Sys/Gen/<target>.pia`: every function's C signature, including whether it is variadic, every constant (`O_CREAT`, `EAGAIN`, `SYS_io_uring_enter`), and every struct's size, alignment and field offsets (`sockaddr_in`, `kevent`, `epoll_event`, `io_uring_sqe`). Nothing in it is written by hand.
- **The generated files are checked in, and CI keeps them honest.** A build cross-compiling for a target needs that target's bindings without its SDK, so the files are in the repository. Each CI job regenerates the file for its own platform from the real headers and fails if it differs from the checked-in one. Drift is a red build on the platform that drifted.
- **Contracts are a hand-written overlay.** Headers carry types, not promises, so a contract table beside the generated file says what each manual page guarantees. It has one row per symbol: the manual page, the contract clauses, the Pia modifiers of each parameter (`out mutable [u8]` for `read`'s buffer, `cstr` for a path), the condition that decides a variadic pack (`open` reads `mode` only with `O_CREAT`), and attributes such as `@blocking`. The `posix` metaprogram joins each overlay row with its generated signature and stamps out the declaration, as `bit_family` stamps out `Pia.Core.Bit` ([lib/Pia/Core/Bit.pia](../../lib/Pia/Core/Bit.pia)). An overlay row that names a symbol the header lacks, or whose parameters do not match the generated signature, is a compile error. A symbol with no overlay row is declared without a contract, so it can be called only as `unsafe` ([stdlib.md](../stdlib.md#8-posix-trusted-declarations-and-typed-wrappers)).
- **The overlay is shared, and the generated files are per target.** `@target` picks the generated file ([ADR 0049](0049-targets-are-theories.md)). The overlay's rows hold for both platforms, unless a row is marked for one target. A system call on Linux is a row whose symbol is `syscall` and whose number comes from the generated `SYS_` constant, so no number is written by hand. macOS has no system-call rows, because the library goes through libSystem there.
- **The trust report lists overlay rows.** Every generated declaration is a trusted foreign contract. The report names its overlay row and manual page, and the header and target it was generated from, so an audit reads the overlay.

## Implementation steps

1. **Foreign bindings first** (section 6), since ADR 0050's I/O stack and `Pia.Sys` (#55, #57) need them: `tools/bindings` and the generated files for both targets, the CI regeneration check, the contract overlay and the `posix` metaprogram, and variadic calls. Until packs exist (step 3), an overlay row with a pack is stamped out as one fixed declaration per arity (`open` and `open_mode`), with the variadic ABI. That restriction is internal to the bindings and goes away in step 4.
2. **Core tuples** (section 1): syntax, sema as anonymous records, IRGen, codegen and the verifier through the record paths, patterns, `t.0`, `t.[type]`, and the structural instances.
3. **Pack parameters and calls** (section 2): `...ts` parameters, deduction, the argument-collection rule, partial application from the expected type, `...t` spreading, and `All` and `CPromoted`.
4. **Walking packs** (sections 3 and 4): `elements` and `tuple_of`, `for` over a pack with its expansion, the proof against an abstract element, and unrolled codegen. Foreign packs replace the per-arity declarations.
5. **`Pia.Core.Pack` and `Pia.Fn`'s combinators**: `map`, `fold`, `apply`, `cat`, `get` and `zip`; `bind_front`, `bind_back`, `compose`, `flip` and `unpack`, with `Function` over packs; and `Pia.Text.Format` on top.
6. **Variadic types** (section 5): pack type parameters, then `one_of` with type-pattern `match`.

## Consequences

- A variadic call looks like any other call, partial application included, and a variadic definition looks like an ordinary loop. The only new syntax is `...` on the pack parameter and on a spread argument.
- There is no recursion over packs, in types or in code. Type-level work is list metaprogramming, and code-level work is a loop that expansion unrolls.
- Variadic code is proved and checked once, at its definition. Each call still compiles to straight-line code.
- `one_of` is a core anonymous sum read by matching on types, so `std::variant` needs no constructor names, no `visit` function and no index-based access.
- Calls to C varargs are typed by their arguments, checked against C's promotion rules, and constrained by contracts, with the ABI right on both targets.
- Foreign signatures, constants and layouts cannot drift from the platforms, because CI regenerates them from each platform's headers. Only the contracts are written by hand, and the trust report audits them.

## Answers

Dean's answers to the first revision's questions (2026-11-23):

1. **Partial application of variadic functions** is wanted, with higher-order functions and combinators. Section 2 does this through the expected type, with `bind_front` and friends for function values that keep the pack open.
2. **`...` rather than `..`.** `..` is already the range operator, and open-sided ranges are planned (`u32{1..}`, #153). A prefix `..n` range would then read the same as a spread `..n` in `f ..n`. `...` costs one token, cannot clash with any range, and is what C++ and JavaScript readers expect for packs and spreads.
3. **Index by type, and `match` on the alternatives.** `xs.[u8]` indexes a pack by type, since types are values. `one_of` is read by a `match` on the active element's type (section 5), not through positional constructors.
4. **Generate the bindings from the headers** to avoid drift, with contracts in a hand-written overlay (section 6).

## Questions for Dean

1. **Distinct element types in `one_of`.** The recommendation is to require them, so that a type names exactly one alternative, and to use a named variant when two alternatives share a type. The alternative is to allow duplicates and add positional arms (`| at 0 x`) for them.
2. **`let g = print w` with no expected type** is a complete call that prints nothing. The recommendation is to keep that rule, with a lint when a variadic call's `unit` result is bound to a name, since that is probably a mistake. The alternative is to make such a binding an error.

## Prior art

| Source | What Pia takes |
| --- | --- |
| C++11 parameter packs, C++17 fold expressions, C++26 pack indexing | the capabilities: variadic functions and types, folds, size and indexing |
| C++ `std::tuple`, `std::apply`, `std::variant` | tuples as the pack value, `apply`, sums over a type list |
| C++'s `std::bind_front`, Haskell's `uncurry` | combinators over argument lists |
| Zig's `inline for` over tuples and `comptime` type lists | a loop over a pack unrolled per element, and types computed by ordinary compile-time code |
| Rust's `libc` crate and `bindgen` | per-target bindings generated from headers, and why types from headers are not contracts |
| Go's `zerrors_*` and `zsysnum_*` tables, generated per platform | constants and system-call numbers as per-target data, checked against the platform |
| GCC's `format` attribute | argument checking for format strings, here as a proved `requires` |
