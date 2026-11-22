# 44. Function values: typed and generic lambdas, a Function concept, and proofs through function arguments

Date: 2026-11-22

Status: Proposed. Dean chose question 1 (2026-11-22): a function object is any type whose module defines `apply`.

## Context

Pia's design has always had function values. A nameless `let` is a function literal, `let (x) => x * x`, with no `fun` or `lambda` keyword, and function literals are curried ([design.md](../design.md)). The parser reads them, and metaprograms run them in the interpreter: every operator in the prelude is one. Ordinary code cannot use them. IRGen has no lowering for `Lambda` outside `with_arena`, and the tour lists function values under "Designed but not built yet".

The C++23 standard library ([ADR 0040](0040-cpp23-standard-library-in-pia.md)) is blocked on them: predicates, comparators and operations for `<algorithm>` and `<numeric>`, `<ranges>` views, `<functional>`, and the monadic operations of `option` and `result`. Dean has set two requirements for that work (2026-11-22):

- **No `_if` variants.** `find`, `count`, `remove`, `replace`, `copy`, `sort` and `accumulate` are each one overload set, with overloads that take a value and overloads that take a function (ADR 0040, section 6). So overload resolution ([ADR 0034](0034-concepts-and-overload-resolution.md)) must tell a value of type `t` from a function `t -> bool` cleanly.
- **A standard `Function` concept** matches function objects, lambdas and plain functions alike, and the library's predicate overloads are constrained on it.

The library thread also needs:

1. a callee's `ensures` to mention its predicate, as in `find`'s `ensures result < len xs ==> p xs.[result]`, which needs function arguments to be pure and total;
2. a callee to require a law of its comparator, such as a strict weak order for `sort`;
3. `find xs (let (x) => x > 3)` to compile to the same vectorised loop as a hand-written one.

Other constraints come from earlier decisions: fewer keywords is better; generic parameters are `(t : type)` with deduction (ADR 0034, [ADR 0035](0035-substitution-failure-and-total-constraints.md)); generic definitions are to be proved once ([ADR 0043](0043-generic-definitions-proved-once.md)); there is no garbage collection ([ADR 0026](0026-memory-manager.md)); and captured values must respect ownership and borrows ([ADR 0042](0042-lifetimes-liveness-and-escape-analysis.md)).

### Prior art

- **C++** gives each lambda its own unnamed closure type with an `operator()`. Templates over the callable type monomorphise and inline, which is why `std::find_if` with a lambda vectorises. `std::function` is the separate, type-erased, allocating form. C++20 generic lambdas (`auto` parameters, or `[]<typename T>`) are lambdas with a template `operator()`.
- **Rust** does the same with `Fn`, `FnMut` and `FnOnce` traits, `impl Fn` arguments and results, and `Box<dyn Fn>` for the dynamic form. Captures are inferred by use: by reference, by mutable reference, or by move.
- **Dafny** and **Why3** treat function values in specifications as total mathematical functions; Dafny's `f.requires(x)` and `f.reads` expose a function value's contract. **Verus** gives closures `requires` and `ensures` clauses that the caller can rely on through `f.requires` and `f.ensures`.
- **OCaml** has closures as heap values, which Pia cannot copy without a garbage collector.

## Decision

Function values are static by default, as in C++ and Rust: every lambda has its own type, a function parameter is a constrained type parameter, and each call with a lambda is a separate instance that codegen inlines. The proof follows ADR 0043: a higher-order function is proved once, with its function argument abstract and constrained by the contract of its parameter's type, and each argument is checked against that contract where it is passed.

### 1. Lambdas

A lambda is a nameless `let`, as today. It may carry types, modifiers, a result type and contracts, in the same places a named function does:

```ocaml
let square = let (x : i32) => x * x
let next = let (x : u8) : u8 requires x < 255 ensures result = x + 1 => x + 1
let between (lo : u8) (hi : u8) = let (x : u8) => lo <= x && x <= hi
```

The grammar gains the result type and the contracts:

```ebnf
lambda = "let" lparam { lparam } [ ":" annot ] { contract } "=>" seq ;
```

A lambda is curried like any function: `let (a) (b) => a + b` applied to one argument is a lambda of one parameter.

A lambda's body is its definition. Where a lambda is in scope, the verifier knows what it computes, as it does for pure scalar functions today (#202), so most lambdas need no contract. A written `requires` restricts where it may be called, and a written `ensures` is checked against the body like any postcondition.

### 2. Typed and generic lambdas

A lambda's parameters may be typed, untyped or explicitly generic.

- **Typed:** `let (x : u8) => x > 3` has type `u8 -> bool`.
- **Untyped, with an expected type:** where the lambda is an argument, or bound by a `let` whose type is written, the parameter types come from the expected type. In `find xs (let (x) => x > 3)` with `xs : [u8]`, `x` is a `u8`, deduced exactly as a generic argument is deduced from the expected type (ADR 0034).
- **Untyped, with no expected type:** `let gt3 = let (x) => x > 3` is a generic lambda, like a C++ `auto` lambda. Each untyped parameter is an implicit type parameter, and each use instantiates it. Its body is checked and proved per instance, as generic code was before ADR 0043, because there is no concept to prove it against. A lint ([ADR 0037](0037-idiomatic-pia-and-lints.md)) suggests a type, or an explicit generic form, for a generic lambda that is exported or used at more than one type.
- **Explicitly generic:** `let (t : type where Ord t) (a : t) (b : t) => less a b` has type parameters like a generic function, deduced at each application and constrained by concepts. A constrained generic lambda is proved once, against its concepts, by ADR 0043.

### 3. Function types

The arrow type that the grammar already has is the type of a function value. Its parameters may be named, and the whole arrow may carry contracts that talk about them and about `result`:

```ocaml
(p : t -> bool)
(f : (x : u8) -> u8 requires x < 255 ensures result > x)
(less : (a : t) -> (b : t) -> bool)
```

```ebnf
arrow_type = arrow_dom "->" type { contract } ;
```

The contracts belong to the innermost arrow, so for a curried `(a : t) -> (b : t) -> bool` they may name both `a` and `b`, and they apply once both are given. Modifiers on the parameters are written as for named functions: `borrowed in [u8] -> usize`.

A function type is a type like any other, with two exceptions. Function types never meet `Eq`, `Ord` or `Hash`, since Pia has no function equality. And a function type in a parameter's position is not one type but any type that meets `Function` (section 4).

### 4. The `Function` concept

`Function` is a standard concept, in the prelude, defined with ADR 0034's syntax:

```ocaml
let meta Function (f : type) (a : type) (r : type) : concept = sig
  let apply : (g : f) -> (x : a) -> r
end
```

A type `f` meets `Function f a r` when a value of it can be applied to an `a` to give an `r`. Three kinds of type meet it:

- **A lambda's type.** Each lambda has its own anonymous type, a record of its captures (section 6), which meets `Function` with the lambda's own parameter and result types. Two lambdas with the same text are still two types.
- **A named function's type.** A top-level function named as a value, `find xs is_digit`, has a singleton type with no fields, which meets `Function` with the function's signature. An overloaded name used as a value is resolved against the expected type, and is ambiguous without one.
- **A function object**, a record or variant whose module defines `apply` for it. Application syntax calls it: for `g : counter_below`, `g x` is `apply g x`. This is how a library type such as a hash functor or a comparator with state is callable.

Curried functions meet `Function` one argument at a time: `t -> t -> bool` is a function to `t -> bool`, so a two-argument function object writes `apply (g : f) (a : t) (b : t) : bool`, which has the signature `f -> t -> (t -> bool)`.

**An arrow type in a parameter is sugar for a constrained type parameter.** In

```ocaml
let find (t : type) (xs : [t]) (p : t -> bool) : usize
```

`p : t -> bool` means a fresh type parameter `f` with `where Function f t bool`, and `p : f`. Writing the constraint out is allowed and means the same thing. Each argument passed for `p` deduces `f` to its own type, so every call is an instance at that lambda or function. A result type written as an arrow, as in `compose`'s, is the same: some type meeting `Function`, whose actual type the compiler knows, like Rust's `impl Fn`.

**Overloading on a value or a function** then needs nothing new. With

```ocaml
let find (t : type where Eq t) (xs : [t]) (v : t) : usize
let find (t : type) (xs : [t]) (p : t -> bool) : usize
```

`find xs 3` is viable only for the first overload: deduction gives `t = u8` from `xs`, and `u8` does not meet `Function u8 u8 bool`. `find xs (let (x) => x > 3)` is viable only for the second, because a lambda's type is not `u8`. Searching a slice of functions for a function is never ambiguous either, since function types do not meet `Eq`. A user adapter that makes a scalar type meet `Function` would make such a call ambiguous, and ADR 0034 reports that ambiguity with both candidates.

### 5. Proofs through function arguments

**Pure function values.** A function value is pure when its parameters are all `in` (no `inout` or `out`) and its body neither writes module state nor calls anything that does. A pure function value whose body is proved to terminate (every `let rec` and loop in it has a measure) is a total mathematical function, and may be applied in contracts and spec functions. A non-pure function value may be passed and called in code, but not in a contract; the verifier reports that as an error at the contract.

**In the callee**, a function parameter is abstract. Each pure function parameter `p` is an uninterpreted SMT function, shared by every application in the body and in the contracts, as ADR 0043 makes concept functions. The arrow's contract is the only fact about it: at each call `p x` in code, `p`'s `requires` is a goal, and its `ensures` is assumed of `p x`. A contract may mention `p x` freely, so

```ocaml
let find (t : type) (xs : [t]) (p : t -> bool) : usize
  ensures result <= len xs
  ensures result < len xs ==> p xs.[result]
  ensures forall (i : usize). i < result ==> p xs.[i] = false
= ...
```

is proved once, whatever `p` is.

**At the call site**, the argument is checked against the parameter's type, and the callee's contract is then usable with the argument substituted for `p`:

1. Under the type's `requires`, the argument's `requires` holds: the callee may call it anywhere the type allows.
2. Under the type's `requires`, the argument's result meets the type's `ensures`. For a lambda this is a proof of its body; for a named function, of its contract.
3. The caller then assumes the callee's `ensures`, in which `p xs.[i]` is the argument applied to `xs.[i]`. A lambda in scope unfolds to its body, so `find xs (let (x) => x > 3)` gives the caller `result < len xs ==> xs.[result] > 3` with no contract on the lambda.

Captured values (section 6) are part of the argument: the lambda in `find xs (between lo hi)` is checked, and unfolds, with `lo` and `hi` as they are at the call.

**Laws of function arguments** are preconditions over spec functions. The library defines them once, in `Pia.Fn`, as spec predicates over function values:

```ocaml
let spec strict_weak_order (t : type) (less : (a : t) -> (b : t) -> bool) : bool =
  (forall (a : t). less a a = false) &&
  (forall (a : t) (b : t) (c : t). less a b && less b c ==> less a c) &&
  (forall (a : t) (b : t) (c : t).
     less a b = false && less b a = false &&
     less b c = false && less c b = false ==>
       less a c = false && less c a = false)

let sort (t : type) (xs : borrowed inout mutable [t]) (less : (a : t) -> (b : t) -> bool) : unit
  requires strict_weak_order less
  ensures sorted less xs && permutation xs (old xs)
```

The callee assumes the law, and each caller proves it for its argument. For `sort xs (let (a) (b) => a > b)` over `u8`, the lambda unfolds and the law is a bit-vector fact. For `sort xs less` where `less` met `Ord t`, it follows from `Ord`'s laws. A law used as a precondition is proved where the argument is known, once per call site, and its goal is cached by ADR 0032 like any other.

### 6. Captures

*Amended 2026-11-23: Dean asked for explicit captures, each one copied, borrowed or referenced. This replaces captures inferred from use, which steps 3 and 4 built.*

A lambda lists what it captures, in brackets after `let`, before its parameters. Each capture says how it is captured, with the modifier words Pia already has, so no keyword is added:

```ocaml
let [lo, hi] (x : u8) => lo <= x && x <= hi           \ copied
let [borrowed keys] (k : u32) => contains keys k        \ borrowed
let [inout count] (x : u8) => count <- count + 1; x > 3 \ referenced
```

```ebnf
lambda   = "let" [ captures ] lparam { lparam } [ ":" annot ] { contract } "=>" seq ;
captures = "[" capture { "," capture } "]" ;
capture  = [ "borrowed" | "inout" ] IDENT ;
```

The three modes:

- **Copied**, a bare name: the value is copied into the lambda when it is made. Only copyable values can be copied: scalars, `fixed` records and variants of them, never a buffer, a linear value or a `drop` value. Later changes to a `mutable` variable are not seen by the lambda, and the lambda cannot assign it.
- **Borrowed**, `borrowed x`: a shared, read-only loan of `x`. The lambda's type holds a lent type, so it borrows from `x` exactly as a record holding `borrowed(m)` would (#70, [ADR 0042](0042-lifetimes-liveness-and-escape-analysis.md)): it cannot outlive `x`, and `x` cannot be moved or written while the lambda is live. The loan ends at the lambda's last use. Any value can be borrowed, scalars included.
- **Referenced**, `inout x`: an exclusive, writable loan of a `mutable` variable. The lambda may read and assign `x`, and its writes are seen by the enclosing code after the lambda's last use. While the lambda is live, nothing else may read, write or move `x`, which is the exclusive form of the same loan rule. A lambda with a referenced capture has an effect, so it is not pure (section 5): it can be called in code but not in a contract, and a higher-order function may take it only for a parameter whose arrow is marked as effectful (below). This replaces the "writing through a capture is not allowed" rule of the first version.

A free variable of the body that is not in the list is an error that suggests the three forms: "'lim' is used but not captured: add it to the capture list as [lim] (copied), [borrowed lim] or [inout lim]". Listing a name twice, or listing one the body never uses, is also an error. A lambda with no captures has no list, so `let (x : u8) => x > 3` is unchanged. Top-level functions, constructors and other module items are not captures, since they are not values of the enclosing scope.

**Effectful arrows.** A parameter that accepts lambdas with referenced captures writes `inout` before its arrow: `(f : inout t -> unit)`. Inside the higher-order function such a parameter is called only in code, never in a contract, and its calls are ordered as written. A pure lambda may be passed for an effectful arrow, but not the reverse. This is what `for_each` with state needs; the effects follow-up in section 8 is reduced to effects through `inout` parameters of function types, which this covers for captures.

**Moved captures** stay step 7: `moved x` in the list, which makes the lambda own `x` and gives its type `drop` or linearity like a record holding it.

A lambda's type is still a record with one field per capture, of the captured value for a copy and a lent type for a loan. A lambda that captures nothing is a type with no fields, and costs nothing to pass.

### 7. Code generation

Each instance of a higher-order function at a lambda or named function is an ordinary function in which `p x` is a direct call to the lambda's body, with the lambda's captures as extra arguments. Codegen inlines small ones, as it does any small callee, so `find xs (let (x) => x > 3)` becomes the same loop, and the same vector code, as writing the comparison into `find` by hand. There is no function pointer and no heap allocation for a static function value, ever.

A lambda's type is private to the module that defines it. A module can export a function whose result is an arrow type, but the importer sees it as an opaque type meeting `Function`, and gets the instance through the interface ([ADR 0039](0039-module-and-interface-syntax.md)) as it gets other generic instances.

### 8. What this ADR does not decide

- **Dynamic function values**, a value whose function is chosen at run time from different lambdas, such as a table of handlers. That needs a type-erased value, a code pointer and an environment, and with no garbage collector it must take an explicit allocator. It is the library's `box` over a concept, `box (Function a r)`, decided in [ADR 0046](0046-box-over-a-type-or-a-concept.md), so there is no separate `std::function` type. An arrow type in `box`'s position is sugar for `Function` at that arrow, contract included. A call through a box may appear in a contract only when the arrow is pure; otherwise it is code-only, with its facts from the arrow's contract (ADR 0046, section 5). An `if` that picks between two lambdas of the same type is not dynamic and needs no box.
- **Effects through function values** beyond referenced captures (section 6): `inout` and `out` parameters inside function types.
- **Recursion through function values**, such as a fixed-point combinator. A lambda cannot name itself; a recursive helper is a named `let rec`.

## Implementation order

Each step is a PR with lit tests in `tests/verify` and `tests/codegen`, and the tour's "Designed but not built yet" entry shrinks as it goes.

1. **Typed lambdas and named functions as arguments**, with no captures. Arrow-typed parameters are instantiated per argument (`find<lambda@file.pia:12:9>`), the argument is checked against the arrow's contract, and the lambda unfolds at the caller. The verifier sees instances only, as generics did before ADR 0043.
2. **The `Function` concept and overloading on a function**: arrow parameters become constrained type parameters, function objects with `apply`, application syntax for them, and the value-or-function overload sets the library needs.
3. **Captures by copy and by borrow**, with the lambda's type as a record of its captures and ADR 0042's loan rules. Built inferred (PR #227); step 3b makes the list explicit and adds referenced captures and effectful arrows.
4. **Generic lambdas**: untyped parameters from the expected type, implicit type parameters when there is none, and explicit `(t : type)` parameters.
5. **Laws of function arguments** in `Pia.Fn` (`strict_weak_order`, `equivalence`, `associative` and friends), with the library's `sort` and `accumulate` using them.
6. **Proved once**: function parameters as uninterpreted functions in ADR 0043's abstract encoding, so a higher-order function is proved at its definition and each instance is discharged by the argument's check.
7. **Partial application, lambdas as results, and moved captures**: `add 1`, `compose f g`, and lambdas that own what they capture.

Steps 1 and 2 are what the standard library needs first, for `find`, `count`, `all_of` and the comparator overload of `sort`. Steps 3 and 4 follow, because predicates usually capture a bound and rarely spell out their types.

## Consequences

- The library can write one overload set per algorithm, as Dean asked, and a predicate overload is constrained on `Function` like any other generic.
- A call with a lambda costs what the loop costs. Monomorphisation does mean one instance per lambda, so code size grows with the number of distinct lambdas, as in C++ and Rust. Step 6 makes their proofs cost one check per argument, not a re-proof of the algorithm.
- Contracts can be written about predicates and comparators directly (`p xs.[result]`), because function values are pure and total unless they reference a capture, which marks them effectful and keeps them out of contracts.
- Laws such as strict weak ordering are ordinary preconditions. They are proved per call site, where a concrete lambda makes them decidable bit-vector facts, rather than being restated as contracts on every caller.
- Captures are written out, so what a lambda copies, borrows or references is visible at the lambda, at the cost of a short list on every lambda that captures.
- There is no dynamic function value in the core. Code that needs one waits for `Pia.Fn`'s boxed type and passes it an allocator.

## Questions for Dean

1. **Function objects.** Should a function object be any type with an `apply` function in its module, called with ordinary application syntax (recommended), or should it need an explicit `@derive(Function)`-style declaration? *Answered: any type with `apply`.*
2. **Captures.** Should captures stay inferred from use, with no capture list (recommended, since it adds no syntax), or should a lambda list what it captures, as C++ does? *Answered 2026-11-23 by Dean: copy by default (a bare name), with borrowing (`borrowed x`) and mutable references (`inout x`) supported.*
3. **Dynamic function values.** Is a library box in `Pia.Fn` that takes an allocator (recommended) the right home for run-time-chosen functions, or should the core have a built-in dynamic function type? *Settled by ADR 0046: `box (Function a r)`.*
