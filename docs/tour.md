# A tour of Pia

This tour covers the language as `piac` implements it today. Every example on this page is a complete program, and the test suite proves each one with `piac --verify`. The [last section](#designed-but-not-built-yet) shows the parts of the language that are designed but not built yet, and those examples are marked as such.

Pia's syntax is close to OCaml. Comments are `(* ... *)`.

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

let narrow (x : u32) : u8
  requires x < 256
= x
```

Ranges carry facts the prover uses for free. Here the index can never be out of bounds, and the divisor can never be zero, because the parameter types say so:

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
| `assume p` | assumed at that point, without proof |
| `invariant p`, `decreases m` | on a loop: holds at every iteration, and the measure decreases |
| `old e` | in a postcondition, `e` as it was on entry |
| `forall (i in lo..hi). p`, `exists (i in lo..hi). p` | quantifiers, in contracts and assertions |

Calls are checked against contracts, not bodies. A caller proves the callee's precondition and then knows its postcondition, so proofs stay local to each function:

```ocaml
let inc (x : u8) : u8
  requires x < 255
  ensures result = x + 1
= x + 1

let twice (x : u8) : u8
  requires x < 200
  ensures result = x + 2
= inc (inc x)
```

Arithmetic inside a contract is exact mathematics, so a contract can say `a + b` without worrying that it overflows:

```ocaml
let avg (a : u8) (b : u8) : u8
  ensures 2 * result <= a + b
= (a +| b) / 2

let small (xs : [u8]) : bool
  requires forall (i in 0..len xs). xs.[i] < 10
  ensures len xs > 0 ==> xs.[0] < 10
= true
```

## Metaprograms

A metaprogram is a function marked `let meta` that runs at compile time. It takes and returns values, and code is one kind of value: `` `( ... ) `` quotes code, and `$x` splices a value into it. Whatever a metaprogram produces is type checked and proved like code you wrote.

Pia has no built-in operators. Each one is a metaprogram that gives a symbol a precedence and expands it to a function call. The prelude defines the usual ones, such as `let meta operator ( + ) : prec 6 left = let (a) (b) => `( add $a $b )`, and a program can add its own:

```ocaml
let meta operator ( ** ) : prec 8 right = let (a) (b) => `( pow $a $b )

let pow (a : u8) (b : u8) : u8
  requires b <= 1
= if b = 0 then 1 else a

let times : u16 = 2 * 3 ** 1
```

A top-level call of a metaprogram is replaced by the items it returns, and `@derive(x)` on a type calls the metaprogram `derive_x`. Expansion runs to a fixed point, so a metaprogram can generate code that uses other metaprograms:

```ocaml
let meta make_byte () : item = `( let byte = type u8 )

make_byte ()

let wide = type { v : byte; w : u8 } @derive(eq)
```

Quotes are hygienic: names a quote binds are renamed so they cannot capture yours, and free names in a quote refer to where the metaprogram is defined. [Metaprograms](meta.md) describes the interpreter, its builtins and the expansion loop.

## Designed but not built yet

These parts of Pia are designed, and the parser reads most of them, but `piac` does not compile them yet. [Language design](design.md) has the full picture, and [Status](status.md) the order they arrive in.

**Function values.** A nameless `let` is a function literal, and there is no `fun` keyword. Function literals are curried. Metaprograms use them today, as in the operator declarations above, but ordinary code cannot pass functions around yet.

<!-- untested: function values are not implemented yet -->
```ocaml
let square = let (x : i32) => x * x
let compose f g = let (x) => f (g x)
```

**Variants and matching**, and `dyn`, a tagged value whose tags the prover can enumerate:

<!-- untested: variants and match are not implemented yet -->
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

<!-- untested: generics and concepts are not implemented yet -->
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
