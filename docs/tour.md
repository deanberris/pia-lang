# A tour of Pia

This tour covers the language as `piac` implements it today. Every example on this page is a complete program, and the test suite proves each one with `piac --verify`. The [last section](#designed-but-not-built-yet) shows the parts of the language that are designed but not built yet, and those examples are marked as such.

Pia's syntax is close to OCaml. Comments are `(* ... *)`, which nest, and `\` comments to the end of a line. `(** ... *)` is a doc comment. The compiler keeps every comment, so metaprograms and your editor can read them ([Comments and literate programs](#comments-and-literate-programs)).

## Bindings and functions

`let` is the only way to define anything. A top-level `let` with parameters is a function. Each parameter has a type, and so does the result:

```ocaml
let width : u32 = 1024

let area (w : u32) (h : u16) : u64 = w * h

let pixels : u64 = area width 768
```

Function application is by juxtaposition, as in OCaml: `area width 768`. Functions are curried in the design, and every call passes all of its arguments for now.

Inside a function, `let ... in` binds a local value, and `;` sequences expressions:

```ocaml
let sum_of_squares (x : u16) (y : u16) : u64 =
  let xx : u32 = x * x in
  let yy : u32 = y * y in
  xx + yy
```

`let rec` marks a recursive function. The prover sees the recursion, and a `decreases` clause gives the measure that will prove it terminates:

```ocaml
let rec gcd (a : u32) (b : u32) : u32
  decreases b
= if b = 0 then a else gcd b (a mod b)
```

### No shadowing

A binding may not reuse a name that is already in scope: a local, a parameter, a function, a type or a core builtin. So every name in a function means exactly one thing, for you and for the prover. Primes are ordinary identifier characters, and the compiler suggests them when you need a new name for a related value:

```ocaml
let next (x : u8) : u16
  ensures result = x + 1
= let x' : u16 = x in x' + 1
```

### Mutation

Bindings are immutable unless they say `mutable`. A mutable local is assigned with `<-`:

```ocaml
let count_up (n : u8) : u8 =
  let i : mutable u8 = 0 in
  if n > 10 then i <- 10 else i <- n;
  i
```

## Integers

Integers are bounded, and there are no implicit narrowing conversions. The types are `u8` `u16` `u32` `u64` `i8` `i16` `i32` `i64`, `usize` and `isize`, `bool`, and range types such as `int{0..255}`. A range type is an integer whose bounds are part of its type, and it is stored in the smallest machine integer that holds the range.

A literal takes the type its context expects, and a suffix such as `42u8` fixes it. Widening is implicit and always safe. Narrowing is a goal: it must be proved to fit.

```ocaml
let widen (x : u8) : u32 = x

let clamp_byte (x : u32) : u8 = if x < 256 then x else 255
```

The narrowing in `clamp_byte` is proved by the branch it is on.

Ranges carry facts the prover uses for free. Here the index can never be out of bounds, and the divisor can never be zero, because the parameter types say so. A bound on one value belongs in its type rather than in a `requires` clause, so that it travels with the value ([Idiomatic Pia](idioms.md)):

```ocaml
let lookup (lut : [u8; 256]) (i : int{0..255}) : u8 = lut.[i]

let per_tile (n : u32) (tile : int{1..64}) : u32 = n / tile
```

### Overflow is explicit

By default an arithmetic result must be proved to fit its type: this is `@overflow(proof)`. The other modes give overflow a defined meaning, and then there is nothing to prove:

| Mode | On overflow |
| --- | --- |
| `@overflow(proof)` (default) | cannot happen: the compiler proves it |
| `@overflow(wrap)` | wraps around, modulo the size of the type |
| `@overflow(saturate)` | clamps to the type's minimum or maximum |
| `@overflow(trap)` | stops the program |

The mode goes after the result type and applies to the function's arithmetic. The operators `+|` and `-|` saturate whatever the mode is.

```ocaml
let add_px (a : u8) (b : u8) : u8 @overflow(saturate)
  ensures result >= a && result >= b
= a + b

let tick (x : u8) : u8 @overflow(wrap)
  ensures x = 255 ==> result = 0
= x + 1

let brighten (p : u8) : u8 = p +| 40
```

Wrapping and saturating arithmetic are modelled exactly, so the postconditions above are proved too. In loops, LLVM vectorises saturating arithmetic into NEON's saturating instructions, such as `uqadd`.

## Arrays and slices

`[T; n]` is an array of a fixed length `n`, and `[T]` is a slice whose length is known at run time as `len xs`. Both are indexed with `xs.[i]`, and every index is a goal: `0 <= i < len xs`.

```ocaml
let first (xs : [i32; 4]) : i32 = xs.[0]

let last (xs : [u8]) : u8
  requires len xs > 0
= xs.[len xs - 1]
```

`xs.[a .. b]` is a slice of elements `a` up to but not including `b`. It is a view, not a copy: it shares the buffer's storage, so a function that writes a slice writes that part of the buffer, and the verifier knows the rest is unchanged. Its bounds are a goal, `0 <= a <= b <= len xs`. An array also passes where a slice is expected, as a slice of all of it.

```ocaml
let fill (dst : out mutable [u8]) (v : u8) : unit =
  for i in 0..len dst do dst.[i] <- v done

let clear_tail (xs : out mutable [u8]) (n : usize) : unit
  requires n <= len xs
= fill (xs.[n .. len xs]) 0
```

An array literal `[a; b; c]` gives an array its values. At the top level it is a constant table in read-only data, and the verifier knows every value in it:

```ocaml
let squares : [u16; 4] = [0; 1; 4; 9]

let square (i : int{0..3}) : u16
  ensures result = i * i
= squares.[i]
```

Constant data cannot be passed to an `out` or `inout` parameter. For now the elements must be integer literals.

`abort ()` stops the program. Its precondition is `false`, so every `abort` is a goal that it is never reached: it marks a case the contracts rule out.

### Parameter modifiers

Parameters say how a function uses what it is given, on three axes, so a function's signature tells callers and the prover everything about its effects:

| Axis | Options | Default |
| --- | --- | --- |
| Ownership | `borrowed`, `moved` | `borrowed` |
| Access | `in`, `out`, `inout` | `in` |
| Modifiability | `fixed`, `mutable` | `fixed` |

The default is a read-only borrow. Writing to a buffer requires `out` or `inout`, and `mutable`:

```ocaml
let swap (xs : borrowed inout mutable [u8; 2]) : unit
  ensures xs.[0] = old (xs.[1]) && xs.[1] = old (xs.[0])
= let t = xs.[0] in xs.[0] <- xs.[1]; xs.[1] <- t
```

`old e` in a postcondition is the value of `e` when the function was called.

## Records

Types are values in Pia, so a record type is bound with `let` like anything else. Records are values too: they can be built, passed, returned and copied.

```ocaml
let pixel = type { r : u8; g : u8; b : u8; a : u8 }

let opaque (p : pixel) : pixel
  ensures result.a = 255 && result.r = p.r
= { r = p.r; g = p.g; b = p.b; a = 255 }

let luma (p : pixel) : u16 = p.r + p.g + p.b
```

`let byte = type u8` gives another name to a type. A field of a mutable record can be assigned:

```ocaml
let pixel = type { r : u8; g : u8; b : u8; a : u8 }

let without_red (p : pixel) : pixel
  ensures result.r = 0 && result.g = p.g
= let q : mutable pixel = p in
  q.r <- 0;
  q
```

Records have no built-in equality. `@derive(eq)` generates it, as a function with a postcondition that says what it means, so callers can prove things about `p = q`:

```ocaml
let pixel = type { r : u8; g : u8 } @derive(eq)

let same (p : pixel) (q : pixel) : bool
  ensures result ==> p.r = q.r
= p = q
```

Arrays and slices can hold records. The compiler stores them as one buffer per field, so a loop over one field reads contiguous memory and vectorises:

```ocaml
let pixel = type { r : u8; g : u8; b : u8; a : u8 }

let set_alpha (xs : inout mutable [pixel]) (i : usize) (v : u8) : unit
  requires i < len xs
  ensures xs.[i].a = v && xs.[i].r = old xs.[i].r
= xs.[i].a <- v
```

## Variants and match

A variant type lists its constructors, each with at most one payload. `match` takes a value apart. Its arms must cover every constructor, or end with `_`, and an arm that can never be reached is an error. The verifier knows which constructor built a value, so a match on a known constructor picks its arm:

```ocaml
let opt = type | None | Some of u32

let get_or (o : opt) (d : u32) : u32 =
  match o with
  | Some x -> x
  | None -> d

let roundtrip (x : u32) : u32
  ensures result = x
= match Some x with
  | Some y -> y
  | None -> 0
```

A payload's type can be an integer, `bool`, a record, another variant or `unit`. Arrays and slices inside a variant are not supported yet. Patterns are a constructor with a name or `_` for its payload, `()` for a unit payload, a name that matches anything, or `_`.

## Generics

A generic type is a function from types to a type, and a generic function takes type parameters, written `(t : type)`, before its other parameters. Each use names concrete types: `option u8` is an instance of `option`, and a call of `unwrap_or` with an `option u16` calls its instance `unwrap_or<u16>`. Every instance is generated and proved on its own, so each goal is about concrete types. As with any call, a caller knows only what the instance's contract says, so `same` proves from `id`'s `ensures`:

```ocaml
let option = let (t : type) => type | None | Some of t
let result = let (t : type) (e : type) => type | Ok of t | Err of e
let oom = type | OutOfMemory

let unwrap_or (t : type) (o : option t) (d : t) : t =
  match o with
  | Some v -> v
  | None -> d

let first (v : u16) : u16 = unwrap_or (Some v) 0

let id (t : type) (x : t) : t
  ensures result = x
= x

let same (v : u8) : u8
  ensures result = v
= id v

let reserve (n : usize) : result unit oom =
  if n > 4096 then Err OutOfMemory else Ok ()
```

The type arguments are deduced. A constructor takes its instance from the type it is expected to have, as `Err OutOfMemory` does from `reserve`'s result, or else from its payload, as `Some v` does. A call takes them from its arguments, then from the type it is expected to have. To force a choice, give them: `unwrap_or<u16> (Some v) 0`, or by name, `unwrap_or<t = u16>`. A generic function needs its return type written, and recursive generic types, such as a list, are not supported yet.

### Concepts

A concept says what a type must provide. It is a metaprogram that returns a signature: each requirement is a function a type must have, a law is a lemma every type must prove, and `include` brings in another concept. A constraint on a type parameter, `(t : type where Ord t)`, names one:

```ocaml
let meta Same (t : type) : concept = sig
  let same : (a : t) -> (b : t) -> bool
  let lemma reflexive (a : t) ensures same a a
end

let meta Ord (t : type) : concept = sig
  include Same t
  let less : (a : t) -> (b : t) -> bool
  let lemma irreflexive (a : t) ensures less a a = false
end

let same (a : u8) (b : u8) : bool
  ensures result <==> a = b
= (a = b)

let less (a : u8) (b : u8) : bool
  ensures result <==> a < b
= (a < b)

let max (t : type where Ord t) (a : t) (b : t) : t =
  if less a b then b else a

let biggest (a : u8) (b : u8) : u8 = max a b
```

A type meets a concept when a function with each requirement's name and exact type is in scope, so `u8` meets `Ord` through the two functions above. Each law is then proved for `u8`, from those functions' contracts. A call with a type that does not meet a constraint is an error that says what is missing: `bool does not meet Ord: no function 'same : bool -> bool -> bool' (from 'include Same')`. A generic body may use only what its constraints promise, and that is checked where the generic is written: with `(t : type where Same t)`, a call `less a b` is an error that suggests constraining `t` by `Ord t`, even if no caller has used the generic yet.

An adapter supplies a concept's requirements for a type that does not meet it, or meets it in a way a caller does not want. Its functions are reached only through it, never by their own names:

```ocaml
let meta Same (t : type) : concept = sig
  let same : (a : t) -> (b : t) -> bool
  let lemma reflexive (a : t) ensures same a a
end

let pixel = type { r : u8; g : u8 }

let adapter by_red : Same pixel = struct
  let same (p : pixel) (q : pixel) : bool
    ensures result <==> p.r = q.r
  = (p.r = q.r)
end

let alike (t : type where Same t) (a : t) (b : t) : bool = same a b

let red_alike (p : pixel) (q : pixel) : bool = alike p q
```

A type that meets a concept directly uses its own functions. An adapter is used when the call names it, as in `alike<Same = by_red> p q`, or when it is the only way the type meets the concept, as here. Its laws are proved about its own functions. Two adapters for the same concept and type, with neither named, are an error that names both.

Functions may share a name when their parameter types differ. They form an overload set, and each call picks the one that fits its arguments best: an exact type beats a conversion, and a function that is not generic beats a generic one. A generic overload whose type arguments do not meet its constraints drops out of the call, so it is only chosen for the types it can serve. Overloads with the same parameter types are told apart by their preconditions, and each call gets the most specific one whose precondition is proved where it is made. The choice is made at compile time, from proofs, and never adds a test at run time:

```ocaml
let pick (x : u8) : u8
  ensures result = 0
= 0

let pick (x : u8) : u8
  requires x < 10
  ensures result = 1
= 1

let by_branch (x : u8) : u8
  ensures (x < 10 ==> result = 1) && (x >= 10 ==> result = 0)
= if x < 10 then pick x else pick x
```

Their `requires` clauses must be ordered, each overload's including every clause of a less specific one, so the most specific is always well defined. Between two generics that both fit, the one whose parameter types are an instance of the other's wins (`pair t t` over `pair a b`), and then the one whose constraints entail the other's: a `rank` for `Ord t` beats a `rank` for `Same t` when the type meets both, because `Ord` includes `Same`. Two concepts that require the same functions and state no laws entail each other, whatever their names, so two overloads that differ only by them are an error at the second.


## Control flow

`if ... then ... else` is an expression. `&&`, `||` and `==>` short-circuit, so a guard protects what follows it:

```ocaml
let starts_with_zero (xs : [u8]) : bool = len xs > 0 && xs.[0] = 0
```

`for i in lo..hi do ... done` loops over a half-open range, optionally with `step`. `while c do ... done` loops while `c` holds, and can carry an `invariant` and a `decreases` measure:

```ocaml
let add_rows (a : [u8]) (b : [u8]) (dst : out mutable [u8]) : unit
  requires len a = len dst && len b = len dst
= for i in 0..len dst do dst.[i] <- a.[i] +| b.[i] done

let find (xs : [i32]) (x : i32) : usize =
  let i : mutable usize = 0 in
  while i < len xs && xs.[i] <> x
    invariant i <= len xs
    decreases len xs - i
  do
    i <- i + 1
  done;
  i
```

The verifier proves each invariant on entry and after an arbitrary iteration, proves the goals in the body for every iteration where the invariant holds, and knows only the invariant after the loop. A `while` loop needs a `decreases` measure that is never negative and goes down, or its termination is not proved. Both loops above are proved, and `add_rows` becomes a NEON loop that adds 16 bytes at a time. [The verifier](verifier.md#loops) has the details.

## Contracts

A contract is a claim the compiler must prove. Pia has these today:

| Clause | Meaning |
| --- | --- |
| `requires p` | precondition: proved at every call, assumed in the body |
| `ensures p` | postcondition: proved at every return, assumed by callers; `result` is the returned value |
| `assert p` | proved at that point |
| `assume p` | assumed at that point, without proof; only in a file marked `@trusted` |
| `invariant p`, `decreases m` | on a loop: holds at every iteration, and the measure decreases |
| `old e` | in a postcondition, `e` as it was on entry |
| `forall (i in lo..hi). p`, `exists (i in lo..hi). p` | quantifiers, in contracts and assertions |

Calls are checked against contracts, not bodies. A caller proves the callee's precondition and then knows its postcondition, so proofs stay local to each function:

```ocaml
let plus (a : u8) (b : u8) : u8
  requires a + b <= 255
  ensures result = a + b
= a + b

let plus3 (a : u8) (b : u8) (c : u8) : u8
  requires a + b + c <= 255
  ensures result = a + b + c
= plus (plus a b) c
```

Arithmetic inside a contract is exact mathematics, so a contract can say `a + b` without worrying that it overflows:

```ocaml
let avg (a : u8) (b : u8) : u8
  ensures 2 * result <= a + b
= (a +| b) / 2

let below (xs : [u8]) (lim : u8) : bool
  requires forall (i in 0..len xs). xs.[i] < lim
  ensures len xs > 0 ==> xs.[0] < lim
= true
```

## Function values

A nameless `let` is a function literal, a lambda: there is no `fun` keyword. A parameter with a function type, `(p : u8 -> bool)`, takes a lambda or the name of a top-level function. Each call compiles to its own copy of the function with the argument called directly, so a lambda costs what writing its body in the loop would ([ADR 0044](adr/0044-function-values-and-lambdas.md)).

A lambda's body is its definition: where it is passed, the verifier knows what it computes. So `find`'s contract, which mentions `p`, means `x > 3` at this call, and the lambda needs no contract of its own:

<!-- example: find_big.pia -->
```ocaml
let find (xs : [u8]) (p : u8 -> bool) : usize
  ensures result <= len xs
  ensures result < len xs ==> p xs.[result]
= let i : mutable usize = 0 in
  while i < len xs && p xs.[i] = false
    invariant i <= len xs
    decreases len xs - i
  do i <- i + 1 done;
  i

let first_big (xs : [u8]) : usize
  ensures result < len xs ==> xs.[result] > 3
= find xs (let (x : u8) => x > 3)
```

A function type can carry a contract that names its parameters and `result`. The function that takes it may call it wherever its `requires` holds and relies on its `ensures`, and every argument is proved to meet both. A lambda may also give a result type and contracts before its `=>`:

```ocaml
let apply_twice (x : u8) (f : (y : u8) -> u8 requires y < 200 ensures result > y) : u8
  requires x < 100
  ensures result > x
= let a = f x in
  if a < 200 then f a else a

let plus2 (x : u8) : u8
  requires x < 100
  ensures result > x
= apply_twice x (let (y : u8) : u8 requires y < 250 => y + 1)
```

A **function object** is any record or variant whose module defines `apply` for it. Applying it, `g x`, calls `apply g x`, and it can be passed wherever a function is expected, carrying state in its fields. `Function`, a standard concept, is what all of these meet, and a generic can say so itself, `(f : type where Function f t bool)`. A name may have one overload that takes a value and one that takes a function: a lambda, a named function or a function object only fits the second, and anything else only the first.

<!-- example: find_either.pia -->
```ocaml
let meta Eq (t : type) : concept = sig
  let same : (a : t) -> (b : t) -> bool
end

let same (a : u8) (b : u8) : bool = (a = b)

let find (t : type where Eq t) (xs : [t]) (v : t) : usize
  ensures result <= len xs
= let i : mutable usize = 0 in
  while i < len xs && same xs.[i] v = false
    invariant i <= len xs
    decreases len xs - i
  do i <- i + 1 done;
  i

let find (t : type) (xs : [t]) (p : t -> bool) : usize
  ensures result <= len xs
  ensures result < len xs ==> p xs.[result]
= let i : mutable usize = 0 in
  while i < len xs && p xs.[i] = false
    invariant i <= len xs
    decreases len xs - i
  do i <- i + 1 done;
  i

let below = type { lim : u8 }
let apply (g : below) (x : u8) : bool = (x < g.lim)

let where3 (xs : [u8]) : usize = find xs 3

let first_below (xs : [u8]) (lim : u8) : usize
  ensures result < len xs ==> xs.[result] < lim
= let b : below = { lim = lim } in
  find xs b
```

A lambda **captures** the locals it uses, with no capture list. A scalar is copied when the lambda is made, so later changes to a `mutable` variable are not seen, and a lambda may not assign what it captures. A buffer is borrowed: it cannot be written while the lambda is still used. Each lambda has its own type, a record of its captures that meets `Function`, so passing one costs what passing its captures does, and its body is still known at the call:

```ocaml
let find (xs : [u8]) (p : u8 -> bool) : usize
  ensures result <= len xs
  ensures result < len xs ==> p xs.[result]
= let i : mutable usize = 0 in
  while i < len xs && p xs.[i] = false
    invariant i <= len xs
    decreases len xs - i
  do i <- i + 1 done;
  i

let first_between (xs : [u8]) (lo : u8) (hi : u8) : usize
  ensures result < len xs ==> lo <= xs.[result] && xs.[result] <= hi
= find xs (let (x : u8) => lo <= x && x <= hi)
```

A lambda's parameter types may be left out where it is passed: they come from the parameter's function type, once the other arguments have fixed its type parameters, so `find xs (let (x) => x > 3)` with `xs : [u8]` makes `x` a `u8`. A typed lambda fixes them itself. A `let` of a lambda with untyped parameters and no captures is **generic**, like a C++ `auto` lambda: each use is an instance, proved on its own. A lambda can also take type parameters with constraints, which is proved once over them. A lambda's result type, when not written, comes from its body:

```ocaml
let meta Ord (t : type) : concept = sig
  let less : (a : t) -> (b : t) -> bool
end

let less (a : u8) (b : u8) : bool = (a < b)

let both_small (a : u8) (b : u16) : bool =
  let small = let (v) => v < 100 in
  small a && small b

let smaller (a : u8) (b : u8) : u8 =
  let min = let (t : type where Ord t) (x : t) (y : t) : t =>
    if less y x then y else x in
  min a b
```

Moving a value into a lambda, generic lambdas that capture, and functions stored in data or returned come in later steps of ADR 0044.

## Metaprograms

A metaprogram is a function marked `let meta` that runs at compile time. It takes and returns values, and code is one kind of value: `` `( ... ) `` quotes code, and `$x` splices a value into it. Whatever a metaprogram produces is type checked and proved like code you wrote.

Pia has no built-in operators. Each one is a metaprogram that gives a symbol a precedence and expands it to a function call. The prelude defines the usual ones, such as `let meta operator ( + ) : prec 6 left = let (a) (b) => `( add $a $b )`, and a program can add its own:

```ocaml
let meta operator ( ** ) : prec 8 right = let (a) (b) => `( pow $a $b )

let pow (a : u8) (b : int{0..1}) : u8 = if b = 0 then 1 else a

let times : u16 = 2 * 3 ** 1
```

A top-level call of a metaprogram is replaced by the items it returns, and `@derive(x)` on a type calls the metaprogram `derive_x`. Expansion runs to a fixed point, so a metaprogram can generate code that uses other metaprograms:

```ocaml
let meta make_byte () : item = `( let byte = type u8 )

make_byte ()

let wide = type { v : byte; w : u8 } @derive(eq)
```

Quotes are hygienic: names a quote binds are renamed so they cannot capture yours, and free names in a quote refer to where the metaprogram is defined. [Metaprograms](meta.md) describes the interpreter, its builtins and the expansion loop.

## Comments and literate programs

Comments are part of the program. The compiler attaches each one to the code it describes, and a doc comment, `(** ... *)`, is the documentation that hovering over a name shows in your editor:

```ocaml
(** The number of elements in one SIMD tile. *)
let tile : u32 = 16  \ a NEON register holds 16 bytes

\ Two `\` lines in a row are one comment.
\ Neither is a doc comment.
let tiles (n : int{0..4096}) : u32 = (n + 15) / 16
```

A metaprogram sees the comments too. `listing ()` gives it the program's items, and `doc x` an item's documentation, so a project can insist on documenting everything:

<!-- example: documented.pia -->
```ocaml
(** Fails unless every top-level function has a doc comment. *)
let meta require_docs () : item =
  let check (item : expr) : unit =
    if kind item = "LetItem" && doc item = "" then
      fail (concat (name item) " has no doc comment")
    else () in
  fold (let (acc) (i) => check i) () (listing ())

(** Adds one, saturating at 255. *)
let bump (x : u8) : u8 = x +| 1

require_docs ()
```

A file named `*.pia.md` is a literate program: Markdown whose fenced `pia` blocks are the code. The prose before a block is the documentation of its first item, so the page you read and the program you prove are the same file. [Metaprograms](meta.md#comments-and-literate-programs) lists the builtins, and [ADR 0029](adr/0029-comments-as-syntax-and-literate-pia.md) the rules.

## Designed but not built yet

These parts of Pia are designed, and the parser reads most of them, but `piac` does not compile them yet. [Language design](design.md) has the full picture, and [Status](status.md) the order they arrive in.

**More function values.** Lambdas work today ([Function values](#function-values)). Returning them, partial application and moved captures are designed in [ADR 0044](adr/0044-function-values-and-lambdas.md):

<!-- untested: function results and partial application are not implemented yet -->
```ocaml
let between (lo : u8) (hi : u8) = let (x : u8) => lo <= x && x <= hi
let compose f g = let (x) => f (g x)
```

**`dyn`**, a tagged value whose tags the prover can enumerate, and variants with record or float payloads:

<!-- untested: dyn and float payloads are not implemented yet -->
```ocaml
let shape = type
  | Circle of f32
  | Rect of { w : f32; h : f32 }

let describe (v : dyn) : str =
  match v with
  | (x : u8)  -> "byte"
  | (x : f32) -> "float"
  | _         -> "other"
```

**Generic types and concepts.** A generic type is a compile-time function that returns a type. Constraints are concepts, which are metaprograms and can state laws that every instance must prove:

<!-- untested: concepts are not implemented yet -->
```ocaml
let pair = let (a : type) (b : type) => type { fst : a; snd : b }

let meta Eq (t : type) : concept =
  has_fn t `( eq : $t -> $t -> bool )
  && law `( forall (a : $t). eq a a )

let sum (t : type where Numeric t) (xs : borrowed in [t]) : t = fold add zero xs
```

**Modules and interfaces.** A module exports interfaces, which are symbols with types and contracts. Importers name the interfaces they use and verify against their contracts only, so modules build and prove in parallel. A module's state is one more exported symbol:

<!-- untested: modules and interfaces are not implemented yet -->
```ocaml
interface Stream = sig
  let status = type | Closed | Open | Drained
  let state : status
  let pull : unit -> [u8]
    requires state = Open  ensures state = Open || state = Drained
end
```

**Concurrency and placement.** `spread` is a parallel loop. Collectives such as `halo_exchange` and `all_reduce` are library metaprograms, and the compiler proves that every worker reaches them in the same order. `@place` chooses the CPU or the GPU:

<!-- untested: spread and @place are not implemented yet -->
```ocaml
let sediment_step (grid : borrowed in mutable tiled<cell, 256, 256, halo = 1>) : unit
  ensures total_mass grid = old (total_mass grid) - outflow grid
=
  halo_exchange grid;
  spread tile in grid @place(auto) do
    erode_and_deposit tile
  done;
  record_outflow grid (all_reduce add (map outflow_of grid))
```

**Floats and SIMD vectors.** `f16`, `f32` and `f64` with strict IEEE semantics by default, `@finite` to prove no NaN or infinity appears, and three explicit ways to allow reassociation. `vec<T, k>` fixes a SIMD shape where auto-vectorisation is not enough. **Refinement types** such as `{ y : i32 | lo <= y && y <= hi }` and `where` invariants on records.
