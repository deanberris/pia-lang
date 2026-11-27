# Metaprograms

Status: implemented in M7 ([#8](https://github.com/deanberris/pia-lang/issues/8)). Decisions: [ADR 0007](adr/0007-metaprogramming-fixed-point-expansion.md) and [ADR 0008](adr/0008-operators-via-metaprograms.md).

A metaprogram is a `let meta` function that runs at compile time. It takes and returns values, and syntax is one kind of value. `src/meta` holds the engine: a tree-walking interpreter (`Interpreter.cpp`) and the expansion loop (`Expand.cpp`). Expansion runs after parsing and before Sema, so everything a metaprogram produces is type checked and proved like hand-written code.

`piac --dump-expanded file.pia` prints the syntax tree after expansion. `--dump-ast` still prints it as parsed.

## Operators

Pia has no built-in infix operators. Each one is a `let meta operator` declaration that gives a symbol its fixity and expands it to a call of a core builtin:

```ocaml
let meta operator ( + ) : prec 6 left = let (a) (b) => `( add $a $b )
```

The standard operators live in the prelude ([`src/syntax/Prelude.cpp`](../src/syntax/Prelude.cpp)), which every program imports:

| Level | Operators | Associativity | Builtins |
| --- | --- | --- | --- |
| 1 | `==>` `<==>` | right | `implies` `iff` |
| 2 | `\|\|` | right | `or` |
| 3 | `&&` | right | `and` |
| 4 | `=` `<>` `<` `>` `<=` `>=` | none | `eq` `ne` `lt` `gt` `le` `ge` |
| 5.5 | `<<` `>>` | left | `shl` `shr` |
| 6 | `+` `-` `+\|` `-\|` | left | `add` `sub` `add_sat` `sub_sat` |
| 6.3 | `\|` | left | `bor` |
| 6.4 | `^` | left | `bxor` |
| 6.5 | `&` | left | `band` |
| 7 | `*` `/` `%` `mod` | left | `mul` `div` `rem` `rem` |

Prefix `~x` is built into the parser, like `-x`, and stands for `bnot x`. `|` is bitwise or only inside brackets ([grammar.md](grammar.md#operators)).

The parser reads the fixities from these declarations. A program can declare its own operators, or redeclare a prelude one. When it does, `parseProgram` parses the program again with the new table. An operator nobody declares still parses, with a level from its first character ([grammar.md](grammar.md#operators)), and expansion then reports it as undeclared.

```ocaml
let meta operator ( ** ) : prec 8 right = let (a) (b) => `( pow $a $b )
let pow (a : u8) (b : u8) : u8 = ...
let times : u16 = 2 * 3 ** 1        (* 2 * (3 ** 1) *)
```

Expansion replaces each binary node with the operator's result, innermost first. The new call takes the location of the operator token, so diagnostics and proof reports point where they did before. The builtins can also be called by name, as in `add_sat x y`. IRGen lowers a builtin call exactly like the operator it stands for ([irgen.md](irgen.md#integers)).

`-x` is still built in. Operators declared for a type (`let meta operator ( + ) for vec<T, k>`) are not supported yet.

## The interpreter

Values are integers (128-bit, so every bound of every Pia integer type fits, `u64`'s included; arithmetic that leaves that range is an error, not a wrap), bools, strings, syntax, lists, functions and unit. A metaprogram can use literals, names, application (curried, with partial application), `let ... in` (a local function may recurse), lambdas, `if`, `;`, list literals, quotes, and `+ - * / % mod < > <= >= = <> && ||` on its own values. Inside a metaprogram these operators act on its values directly. They are not expanded.

| Builtin | Meaning |
| --- | --- |
| `map f xs` | apply `f` to each element |
| `fold f init xs` | `f (... (f init x0) ...) xn` |
| `length xs` | the number of elements |
| `fields t` | the field names of the record type item `t`, or of the record type it names, as strings |
| `name t` | the name of an item or a name, as a string |
| `concat a b` | two strings joined (an integer counts as its digits), or two lists |
| `param name type` | a parameter `(name : type)`, for a quote's parameter list; `type` is a type's name or its syntax |
| `nth xs i` | the element at index `i`, counting from 0; outside the list is an error |
| `zip xs ys` | the pairs `[x; y]` of two lists of one length; different lengths are an error |
| `range n` | `[0; 1; ...; n - 1]` |
| `reverse xs` | the elements in the opposite order |
| `filter p xs` | the elements for which `p` returns `true` |
| `product xss` | every list that takes one element from each list of `xss`, the first varying slowest |

Each expansion has a fuel budget of a million steps. Running out is an error.

## Type-level metaprograms

A `let meta` whose parameters are all types and that returns a `type` or a `bool` is type-level ([ADR 0035](adr/0035-substitution-failure-and-total-constraints.md)). It stays in the program after expansion, because types and `where` predicates call it while the compiler checks types ([irgen.md](irgen.md#functions)):

```ocaml
let meta widen (t : type) : type =
  if t = u8 then u16 else if t = u16 then u32 else if t = u32 then u64
  else fail (concat "no integer type is wider than " (name t))

let meta small (t : type) : bool = size_of t <= 2

let add_wide (t : type where small t) (a : t) (b : t) : widen t = a + b
```

There, types are values. A type's name, such as `u8` or `pixel`, denotes the type, `=` and `<>` compare types, and `name t` spells one as Pia does (`u8`, `option<u8>`, `[u8]`).

| Builtin | Meaning |
| --- | --- |
| `size_of t` | the bytes a value of `t` takes: an integer the smallest of 1, 2, 4 or 8 that holds its range, a bool 1, an array its elements', a record the sum of its fields'; a slice has no fixed size, which is an error |
| `type_kind t` | `"int"`, `"bool"`, `"unit"`, `"array"`, `"slice"`, `"record"` or `"variant"` |
| `element t` | an array's or a slice's element type |
| `field_types t` | a record's field types, or a variant's payload types, as a list |
| `type_args t` | a generic instance's type arguments, as a list (empty for any other type) |
| `type_named s` | the type named `s`, as `Pia.Text.Json.Derive`'s `json_errors` names the error type a derive defined |
| `eq ne lt gt le ge add sub mul div rem and or implies iff` | the core builtins that a `where` predicate's operators expand to |

`match` takes a type too, which reads better than a cascade of `if`s:

```ocaml
let meta widen (t : type) : type =
  match t with
  | u8 ensures size_of result = 2 -> u16
  | u16 -> u32
  | u32 -> u64
  | _ -> fail (concat "no integer type is wider than " (name t))

let meta small (t : type) : bool =
  match t with
  | int -> size_of t <= 2
  | [e; n] requires n > 0 -> n <= 16 && small e
  | option e -> small e
  | _ -> false
```

- A type's name matches that type, and `int` every integer type. `[e]` matches a slice and `[e; n]` an array, binding the element type and the length. A generic's name applied to patterns, as in `option e`, matches its instances, binding their type arguments. `record fs` and `variant cs` bind the list of field or payload types. Any other name binds the whole type, and `p as x` binds it as well as matching `p`.
- Types are an open set, so a match on a type must end with a catch-all.
- An arm's `requires` is not a guard: if a type reaches the arm and it does not hold, that is an error (or, during overload resolution, the candidate's reason). An arm's `ensures` is checked of the arm's value, `result`, when the arm is taken.
- The same arm contracts work on a value `match` in ordinary code, where they are proof goals ([irgen.md](irgen.md#variants)).

A metaprogram that runs during expansion has no type values: a type's name there is an unknown name, as before.

A type-level metaprogram that a type or a constraint uses must terminate, so that which overloads a call can choose never depends on the step budget. The compiler checks this where it is defined, and an error is reported only where one that may not terminate is used:

- it may call the builtins, except `listing` and `redefine`, and other type-level metaprograms that terminate;
- a recursive call must be on a component of a type parameter, in one parameter position that all its recursive calls share: `element t`, an element of `field_types t` or `type_args t` that `map` or `fold` hands to a lambda, a name that a `match` on `t` binds below its top (`e` in `[e]` or `option e`), or a component of one of those. Types are finite trees, so this always ends;
- local functions may not recurse, it may refer to itself only by calling itself, and a cycle of metaprograms calling each other is rejected (it would need a measure they all decrease, which is not supported yet).

```ocaml
let meta plain (t : type) : bool =
  if type_kind t = "int" || type_kind t = "bool" then true
  else if type_kind t = "array" then plain (element t)
  else if type_kind t = "record" then
    fold (let (ok) (f) => ok && plain f) true (field_types t)
  else false
```

Running out of steps in such a metaprogram is an internal compiler error.

## Quotes and splices

`` `( ... ) `` builds syntax: an expression, one item, or several items. Inside a quote:

- `$x` splices the value of `x`. Syntax is copied in. A string becomes a name, or a type name in a type position such as `(a : $t)`. A type item in a type position becomes its name. An integer becomes a literal, and a bool becomes `true` or `false`.
- `$(e)` splices the value of the expression `e`.
- `$x` in a binder or field position (`let $n`, `a.$f`, a quantifier's `exists ($n : t)`) splices a string, or the name of an item, as that name.
- `$ps` alone in a parameter list, as in `let lemma $n $ps : unit = ()`, splices a list of parameters made by `param`, so a metaprogram can make a function with as many parameters as it needs. The prelude's `litmus` uses it for a test's registers.
- `[ $xs ]` splices a list's elements into a list literal, `{ $fs }` a list of `[name; value]` pairs into a record literal's fields, `type { $fs }` a list of `[name; type]` pairs into a record type's, `| $c of t` a string as a constructor's name, `type | $cs` a list of names and `[name; type]` pairs as a variant's constructors, and `| $c x -> ...` one as the constructor a pattern matches, so a derive can write bytes it computed, build a value of the type it was given, declare the records it needs, make an error set with one constructor per field it found, and name and match its own constructors (`tests/meta/list_splices.pia`). A nullary constructor in a quoted pattern is written `$!None`, since a bare name there is a variable that hygiene renames. `with $f` after a quoted function's contracts reveals the opaque spec function a metaprogram named, so a derive can keep the spec functions it writes opaque and reveal each only where it is proved (`tests/meta/reveal_splice.pia`).

The code a quote builds takes the location of the expansion site: the operator, the `@derive` attribute, or the top-level call. Spliced code keeps its own locations.

## Hygiene

The rules are [ADR 0022](adr/0022-metaprogram-hygiene.md). Pia has no shadowing: a binding written in the source may not reuse the name of a local in scope, a function, a type or a core builtin. So an unqualified name always means its one visible binding. On top of that, hygiene keeps a quote from capturing, or being captured by, names at the expansion site:

- **Names a quote binds are renamed.** A `let ... in`, a parameter, a lambda or loop variable, or a quantifier binder inside a quote gets a fresh name such as `t#1`, so code spliced into its scope still sees the caller's `t`. The names of quoted top-level items are not renamed, since they are meant to be used.
- **Free names refer to the definition site.** A free name in a quote is marked `[prelude]` when it is a core builtin, and `[toplevel]` otherwise. IRGen resolves a `[prelude]` name to the builtin and a `[toplevel]` name to a top-level function, never to a local. With modules (M8), these become module-qualified paths such as `prelude.add`.
- **Operators and derives for a type will use argument-dependent lookup.** They are found in the module that defines the type and in adapter modules the program imports. Two candidates are an ambiguity error. This arrives with modules.
- **`$!name` opts out.** It stands for the plain name `name`, bound or resolved where the code lands. `derive_eq` uses it for the parameters `a` and `b`, which two separate quotes share:

```ocaml
let meta derive_eq (t : type_decl) : item =
  let n = concat "eq_" (name t) in
  let c = fold_and (map (let (f) => `( $!a.$f = $!b.$f )) (fields t)) in
  `( let $n ($!a : $t) ($!b : $t) : bool ensures $!result <==> $c = $c )
```

## Theory-building metaprograms

`let theory T = gen args` runs the metaprogram `gen` ([ADR 0036](adr/0036-library-theories.md), step 5). It returns a list of items: exactly one `let theory ... = sig ... end`, under any name, and any number of models of it (`let model m : ... = struct ... end`) and other items. The theory is named `T`, and the models are models of `T`.

```ocaml
let conn_state = type | Closed | Open | Draining

let theory Conn = machine "conn" conn_state Closed
  [ edge Closed "connect" Open
  ; edge Open "send" Open
  ; edge Open "shutdown" Draining
  ; edge Draining "close" Closed ]
```

- **Total and pure.** What the metaprogram returns becomes hypotheses of proofs, so it must terminate and read nothing of the program, by the rules for type-level metaprograms ([ADR 0035](adr/0035-substitution-failure-and-total-constraints.md), `src/meta/Totality.cpp`). It may not recurse except on a component of a parameter, may not call `listing` or `redefine`, and the same holds for the metaprograms it calls. A violation is an error at the `let theory` that says why.
- **Arguments.** In a top-level call, the name of one of the program's items stands for that item, and a variant's constructor stands for its name. So `conn_state` above is the type item and `Closed` is the name `Closed`.
- **Quotes of theories.** A quote can hold `let theory`, `let model` and theory members (`let sort`, an abstract `let spec f : ...`, `let axiom`). In a theory's or a model's body, `$xs` splices a list of members. `let sort $s`, `let spec $f` and `let axiom $n` splice names.
- **Hygiene.** The members' names are kept, since they are meant to be used. Their parameters and binders are renamed as in any quote ([Hygiene](#hygiene)).
- **One theory per argument tuple.** A second `let theory U = gen args` with the same call, written the same way, does not build again: `U` is another name for the first theory, so `U.x` is `T.x`.

The prelude's `machine` builds a state machine's theory and its model from a table of `edge`s ([theories.md](theories.md#state-machines)). It is written in Pia with `map` and `fold`, so it is total.

The prelude's `litmus` is a top-level call that builds a lemma from a litmus test, a small concurrent program given as data: threads of `write`, `read`, `store`, `load`, `swap`, `fetch_add` and `barrier` events, and an outcome of `is` and `final` conditions ([theories.md](theories.md#the-memory-model-rc11)). It writes the test's RC11 consistency as boolean matrices over its events, so the lemma is a finite query.

## Lowerings

`@lower(gen args)` on a function runs the metaprogram `gen`, which returns a string of MLIR, and the string becomes the function's lowering, as if `@lower("...")` were written ([ADR 0065](adr/0065-lowerings-written-in-pia.md), [codegen.md](codegen.md#lowerings-written-in-pia)). Among the arguments, the function's parameters stand for themselves, as names, so `concat "$" (name a)` splices the parameter `a`. There are no type values during expansion, so a shape or an element type is passed as an integer or a string (tests/codegen/lower_meta.pia).

## Tactics

`@by(t args)` on a lemma runs the metaprogram `t`, a tactic, on the lemma's goal ([ADR 0036](adr/0036-library-theories.md), step 6). The tactic gets the goal first, then the arguments. Among the arguments, the lemma's parameters stand for themselves, as names. It returns a list of proof steps, which go before the lemma's body, and the verifier proves them like any others ([verifier.md](verifier.md#solver-strategies-and-tactics)). So a tactic can make a proof possible, or faster, but not wrong.

```ocaml
let meta induction (g : syntax) (on : syntax) : list =
  let args = map (let (p) => if p = name on then `( $on - 1 ) else p) (params g) in
  [ `( if $on > 0 then $(make_call (name g) args) ) ]

let spec count (xs : [u8]) (n : usize) (v : u8) : usize
  requires n <= len xs
  ensures result <= n
  decreases n
= if n = 0 then 0 else count xs (n - 1) v + (if xs.[n - 1] = v then 1 else 0)

let lemma split_count (xs : [u8]) (n : usize) (v : u8) (w : u8) : unit @by(induction n)
  requires n <= len xs && v <> w
  ensures count xs n v + count xs n w <= n
  decreases n
= ()
```

The goal is the lemma, as written, before its operators expand:

| Builtin | Meaning |
| --- | --- |
| `hypotheses g` | the goal's `requires` clauses, as a list of syntax |
| `conclusion g` | its `ensures` clauses, joined by `&&` (`true` when there are none) |
| `params g` | its parameters' names, as strings |
| `name g` | the lemma's name |
| `children x` | the parts of the syntax `x`, as a list: an operator's two operands, a call's function and arguments, an `if`'s condition and branches |
| `op x` | an operator's spelling (`"&&"`), the name a call applies, a name's text, or `""` |
| `make_call f args` | the call of `f` (a name, as a string or syntax) on the list `args` (syntax, or strings for names) |

A step is an expression: a lemma call, an `assert`, an `if` for a case split, or a call or `assert` that instantiates a quantified fact at particular arguments. `` `( fuel 4 ) `` is a hint rather than code: it puts `@fuel(4)` on the lemma. A tactic that returns an item or a value that is not syntax is an error.

**Total and pure.** A tactic writes what a proof assumes, so, as for a theory-building metaprogram, the rules for type-level metaprograms apply ([ADR 0035](adr/0035-substitution-failure-and-total-constraints.md)): it may not call `listing` or `redefine`, and it may recurse only on a component of a parameter. For syntax, the components are the elements of `children p` and `hypotheses p` that `map` or `fold` hands to a lambda, and `conclusion p`. This one recurses on the operands of `&&` and asserts each conjunct of the goal as its own step:

```ocaml
let meta conjuncts (e : syntax) : list =
  if op e = "&&" then fold (let (acc) (c) => concat acc (conjuncts c)) [] (children e)
  else [e]

let meta split (g : syntax) : list =
  map (let (c) => `( assert $c )) (conjuncts (conclusion g))

let lemma each (x : u8) : unit @by(split)
  requires x < 10
  ensures x < 11 && x + 1 < 12
= ()
```

## Comments and literate programs

Comments are syntax ([ADR 0029](adr/0029-comments-as-syntax-and-literate-pia.md), [grammar.md](grammar.md#comments-in-the-syntax-tree)), and metaprograms can read them:

| Builtin | Meaning |
| --- | --- |
| `listing ()` | the program's items in source order, as the current pass found them, then the comments at the end of the file |
| `comments x` | the comments attached to the syntax `x`, in source order |
| `doc x` | the text of the `doc` and `prose` comments leading `x`, joined by blank lines; `""` when there are none |
| `text c` | a comment's text (also a string literal's value) |
| `style c` | `"line"`, `"block"`, `"doc"` or `"prose"` |
| `place c` | `"leading"`, `"trailing"` or `"detached"` |
| `kind x` | the kind of a syntax value, such as `"LetItem"`, `"Apply"` or `"Comment"`, or `"Unit"` for unit, as `variants` gives for a constructor with no payload |
| `with_doc s x` | a copy of the syntax `x` (or the first of a list of items) with a leading doc comment `s` |
| `fail s` | stop with the error `s`, reported at the expansion site |

In the REPL, metaprograms can also change definitions that already exist, through `Pia.Live` ([ADR 0031](adr/0031-verified-repl-and-live-environment.md)). `listing ()` there lists the whole environment.

| Builtin | Meaning |
| --- | --- |
| `redefine x` | the definitions in the syntax `x`, marked to replace the environment's definitions of the same names; the REPL proves the change like a `:redef` cell before it commits it ([repl.md](repl.md#live-redefinition)) |

`piac` has no `Pia.Live`: a compiled program cannot redefine anything, so `redefine` fails there.

Comments survive everything expansion does:

- **Quotes** keep the comments written inside them, at the expansion site like the rest of the quote.
- **Splices** keep the comments on the spliced code. A comment on the splice itself, as in `` `( (** the sum *) $e ) ``, moves to the code that replaces it.
- **Expansion** moves the comments on a replaced node to its replacement: an operator's comments to the builtin call, and a top-level call's comments to the first item it makes.
- **Hygiene** never looks inside a comment. Comments bind no names and refer to none.

A comment can be read but not spliced into code. To document generated code, use `with_doc`, as the prelude's `derive_eq` does, so `eq_pixel` reads "Field-by-field equality for pixel, made by @derive(eq)." on hover.

`tests/meta/doc_lint.pia` walks `listing ()` and fails on an undocumented function, and `tests/meta/literate.pia.md` is a literate program that `piac --verify` proves. Rendering listings to LaTeX, HTML, SVG and DOT ([#63](https://github.com/deanberris/pia-lang/issues/63)) and a Jupyter kernel ([#64](https://github.com/deanberris/pia-lang/issues/64)) build on these.

## Derives

`@derive(x)` on a type item calls the metaprogram `derive_x` with the item and adds the items it returns after the type. The prelude defines `derive_eq`, and for a distinct type `derive_ord`, `derive_add`, `derive_scale` and `derive_bounds` (ADR 0064, section 4), which make `lt_<t>`, `add_<t>`, `mul_<t>` and the rest that `<`, `+` and `*` on the type call. For `let pixel = type { r : u8; g : u8 } @derive(eq)` it makes:

```ocaml
let eq_pixel (a : pixel) (b : pixel) : bool
  ensures result <==> (true && a.r = b.r) && a.g = b.g
  = (true && a.r = b.r) && a.g = b.g
```

`=` on two values of a record type calls `eq_<name>`, and `<>` is its negation. Without the derive, comparing records in code is an error that suggests `@derive(eq)`; in a contract they compare as values ([irgen.md](irgen.md#records)). Because `eq_pixel` has a postcondition, callers can prove facts about `p = q`, such as `ensures result ==> p.r = q.r`.

`Pia.Text.Json.Derive` exports `derive_json` ([ADR 0045](adr/0045-json-derived-codecs-and-conforming-dom.md), steps 4 and 5): `@derive(x)` finds `derive_x` among the program's own metaprograms, or among those its imported interfaces export, and two imported ones of one name are an error that names both. For a record of integers, range types, `bool`, and `option`s (`Pia.Core.Option`) or fixed arrays `[t; n]` of them, it makes:

- `write_json_<t> (dst) (pos) (v : t) : usize`, which writes `v` as a JSON object with `Pia.Text.Json.Write`, one function per member, into room its precondition states as a constant;
- `read_json_<t> (s) (pos) : result <t>_json_read <t>_json_error`, which reads one with `Pia.Text.Json.Read`. It finds a member by a decision tree built at compile time, on the name's length, then on the first byte where the names left differ, then one full compare. It keeps a flag per field, so a member given twice is `Duplicate_<t>` and one never given is `Missing_<t>`, and it checks each integer's range as its digits are read (`Range_<t>`). An unknown member is `Unknown_<t>`, and anything else `Syntax_<t>`, each with its position. The error type has exactly the constructors its type can raise: no `Range_<t>` without an integer field. The value is built only once every field has been read, so it is fully initialised.

A fixed-array field is a JSON array of exactly n values: too few or too many is `Length_<t>`, at the `]` or at the value past the last, and the error type has that constructor only when there is an array field (`tests/std/json_derive_array.pia`, `tests/std/Inputs/json_array_run.pia`). An `option` field writes `null` for None, and reads `null`, or a missing member, as None (`tests/std/json_derive_option.pia`, `tests/std/Inputs/json_option_run.pia`). A member's name is its field's, or `@json(name = "...")` on the field, in printable ASCII with no quote or backslash. The generated code calls the JSON modules by their full paths, so a program that derives `json` imports the interfaces of `Pia.Text.Json.Spec`, `Lex`, `Read`, `Write` and `Derive`. Each derived type also gets `read_json`, the instance of the concept `Json`, so `Json.read<point> text` reads the whole text as a `point`, with only whitespace after it (anything else is `Syntax_point` where the value ends), and `Json.json_errors point`, a type-level metaprogram, is its error type, `point_json_error`; the error constructors still carry the type's name, since constructors are names of the module. `tests/std/json_derive.pia` proves the code it makes, and `tests/std/Inputs/json_derive_run.pia` runs it.

On a variant, `derive_json` follows ADR 0045, section 2. Untagged, the default, each constructor must be told apart from every other by its JSON: a record payload is an object, a number or `bool` payload is that, and a constructor with no payload is `null`; two objects are apart when one requires a member the other cannot have, and two numbers when their ranges do not meet. Any other pair is an error that names the two and suggests a tag. The reader scans an object's members into slots for every object constructor's members, by position, in a function of its own, then picks the one constructor they fit and reads each value with that payload's field readers, so a member whose type differs between constructors is read only once the constructor is known. `@json(tag = "kind")` on the type writes `"kind": "<name>"` first and accepts it anywhere among the members; each payload must then be a record, or none. A constructor's name is its own, or `@json(name = "...")` on it. A record payload, in place or named, derives json too, and the variant's codec calls it (`tests/std/json_derive_variant.pia`, `tests/std/Inputs/json_variant_run.pia`).

Other derives (`ord`, `hash`, `serialise`, `deserialise`) come later. A user can write their own `derive_x`.

A derive reads the type it is given with these builtins, besides `fields`, `constructors` and `range_of` ([ADR 0045](adr/0045-json-derived-codecs-and-conforming-dom.md), step 3). `t` is a type item, or its name as a string:

| Builtin | Meaning |
| --- | --- |
| `field_type t f` | the type of the field `f` of the record `t`, as written, as syntax |
| `variants t` | the constructors of the variant `t`, each `[name; payload]`, with its payload type as syntax, or unit when it has none |
| `attrs t` | the attributes on a type item, or on a function's return annotation, as written, `@derive` included |
| `field_attrs t f` | the attributes on the field `f` of the record `t` |
| `ctor_attrs t c` | the attributes on the constructor `c` of the variant `t` |
| `bytes s` | the UTF-8 bytes of the string `s`, as integers |
| `value x` | the value of a literal's syntax, such as an array type's length: an integer, a bool or a string |

An attribute is `[name; args]`, and each argument `[key; value]`, with `""` as the key of a positional one. A literal argument is its value and a name its spelling as a string, so `@json(name = "x", ignore_unknown)` is `["json"; [["name"; "x"]; [""; "ignore_unknown"]]]`; any other argument is syntax.

A derive's own attributes are its options: `@json(name = "x")` on a field, `| Rect @json(name = "r") of rect` on a constructor ([grammar.md](grammar.md)), or `@json(tag = "kind")` on the type. Once every derive of the type has run, the attributes named after one leave the type, its fields and its constructors, so the rest of the compiler never sees them. An attribute on a field or a constructor that no derive of its type reads is an error that names the derive to add, rather than one that is ignored (`tests/meta/derive_builtins.pia`, `tests/meta/derive_builtin_errors.pia`).

## Generators

A generator is a metaprogram that reads a function's signature and contract and writes tests for it ([ADR 0056](adr/0056-tests-generated-from-contracts-and-theories.md)). Besides `params`, `hypotheses` and `conclusion` (see [Tactics](#tactics)), which work on any function item, it has:

| Builtin | Meaning |
| --- | --- |
| `param_types f` | the type of each parameter of the function `f`, as written, as a list of syntax |
| `return_type f` | `f`'s return type, as written; a function without one is an error |
| `range_of t` | the bounds `[lo; hi]` of an integer type: `u8`, `u64`, `i16`, a range `int{-2..2}`, or a type value |
| `constructors t` | the constructor names of the variant type `t` (an item, or its name), as strings |
| `subst e n v` | the syntax `e` with every name `n` replaced by `v`: syntax, a string (a name), an integer or a bool. Pia has no shadowing, so this cannot capture |

On an item from `listing ()` or a top-level call's argument, the operators have already expanded, so `hypotheses` returns calls such as `le lo hi`, and `conclusion` joins the clauses with a call of `and` too. On a tactic's goal, which is the lemma as written, both keep the operators.

`tests/meta/generators.pia` has a generator that writes one case per combination of its parameters' bounds, and a runner that returns the number of the first case that fails:

```ocaml
let clamp (v : u8) (lo : u8) (hi : int{0..9}) : u8
  requires lo <= hi
  ensures lo <= result && result <= hi
= if v < lo then lo else if v > hi then hi else v

let meta conj (xs : list) : syntax = fold (let (a) (h) => `( $a && $h )) `( true ) xs

let meta check (f : syntax) (r : list) : syntax =
  let res = concat (name f) "_result" in
  let ret = return_type f in
  let call = make_call (name f) (params f) in
  let post = subst (conclusion f) "result" res in
  let body = `( if $(conj (hypotheses f)) then (let $res : $ret = $call in $post) else true ) in
  fold (let (acc) (pv) =>
         let p = nth (nth pv 0) 0 in
         let t = nth (nth pv 0) 1 in
         let v = nth pv 1 in
         `( let $p : $t = $v in $acc ))
       body (reverse (zip (zip (params f) (param_types f)) r))

let meta cases (f : syntax) : list =
  let rows = product (map range_of (param_types f)) in
  map (let (k) => let n = concat (concat (name f) "_case_") (k + 1) in
                  `( let $n () : bool = $(check f (nth rows k)) ))
      (range (length rows))

cases clamp
```

### Tests from contracts

`Pia.Test.Gen` ([ADR 0056](adr/0056-tests-generated-from-contracts-and-theories.md), step 2) packages a generator like the one above. `G.cases f`, after `import Pia.Test.Gen.Gen as G`, writes cases for `f` from its signature and contract, and the verifier decides each one where it lands:

- **Domains.** `edges f` gives each parameter's boundary values: `lo`, `lo + 1`, `0`, `hi - 1` and `hi` of its integer type, `c - 1`, `c` and `c + 1` for each constant `c` its `requires` compares it with, and `false` and `true` for a `bool`.
- **Rows.** `combine doms budget` is their product, or, when the product has more than `budget` rows, a pairwise covering array: every pair of values of every two parameters appears in some row. `cases` uses a budget of 64. A row whose constants make `f`'s `requires` false is dropped. One the constants do not decide keeps the `requires` as a hypothesis.
- **Two lemmas per row.** `f_spec_k`, the **specification check**, says that some value of `f`'s result type meets its `ensures` at the row's inputs. `f_case_k`, the **oracle**, is the `ensures` with the call in place of `result`. Each takes `f`'s parameters with their own types, and its `requires` pins them to the row, so a failed case prints its inputs as the counterexample.

Both lemmas are contracts, so they are read over unbounded integers, as every contract is. `result + 1 = d` on a result of type `int{-3..1}` at `d = 2` is `1 + 1 = 2`, true, where the same expression run as code would overflow. What `cases dec` writes for that row is, by hand:

```ocaml
let dec (d : int{-2..2}) : int{-3..1}
  ensures result + 1 = d
= d - 1

let lemma dec_spec_5 (d : int{-2..2}) : unit @case(spec, dec, 5)
  requires d = 2
  ensures (exists (dec_result : int{-3..1}). dec_result + 1 = d)
= ()

let lemma dec_case_5 (d : int{-2..2}) : unit @case(oracle, dec, 5)
  requires d = 2
  ensures dec d + 1 = d
= ()
```

`@case(spec, f, k)` and `@case(oracle, f, k)` name what a lemma checks, so the report says `case 5: some result can meet the ensures of 'dec'` and `case 5: 'dec' meets its ensures` rather than "the postcondition holds".

**A specification failure** is a contract that no result can meet. `ensures result = a + b` on a `u8` result cannot hold at `a = b = 255`, whatever the body does. For a function with a body, the body's own goals fail too, but for an `extern` nothing else would notice: every proof that assumes its `ensures` there follows from a contradiction, and so does its oracle. So the specification check comes first, and when it fails its goal carries the hint `specification failure: no value of 'f''s result type satisfies its ensures at these inputs`, with the inputs as the counterexample (`tests/std/Inputs/test_gen_spec.pia`). The fix is in the contract: correct the `ensures`, widen the result type, or add a `requires`. An `extern` gets only the specification check, since its oracle can be decided only by running it, which test mode adds (step 3). `tests/std/test_gen.pia` proves the cases of a function with a precondition, a range-typed result, a `bool` parameter, an `extern` and a pairwise array.

## Top-level calls

An item that is a call of a metaprogram, such as `make_byte ()` in column 1, runs it. The items it returns replace the call. A metaprogram may return a list of items, which all replace the call. A metaprogram may also return a call of another metaprogram, which runs in the next pass.

A module exports a metaprogram by listing it in an interface with its result type, as `let meta define : item` ([ADR 0039](adr/0039-module-and-interface-syntax.md)). The interface artifact carries its definition, and an importer runs it by its qualified name, as `R.define "milli" (R.si "milli")`. The names its quotes use are the defining module's: an importer's own `ratio` does not capture `Pia.Core.Ratio.ratio`. The module must define every metaprogram its interfaces list (tests/modules/metaprograms.pia). An exported metaprogram names another module's items in full, as `Pia.Core.Ratio.num` in `Pia.Time`: an alias is the defining module's own, and its importers need not share it. They do import that module's interface. `Pia.Core.Ratio` is built this way.

## The expansion loop

Expansion runs in passes, to a fixed point (design.md, "Stages"). Each pass looks only at the items that existed when it started:

1. Each `@derive` runs.
2. Each top-level metaprogram call runs.
3. Each binary operator expands.

Code produced in one pass expands in the next. So `@derive(eq)` takes two passes: one makes `eq_pixel`, and the next expands the operators inside it.

A metaprogram sees a type only once it is defined. `fields t` on a record whose field types are not all defined yet defers the derive to the next pass. In this program the derive waits one pass for `make_byte` to define `byte`:

```ocaml
let wide = type { v : byte; w : u8 } @derive(eq)
let meta make_byte () : item = `( let byte = u8 )
make_byte ()
```

The loop stops when a pass changes nothing. A metaprogram still waiting then is an error that names the type it needed. `--meta-cycles=N` (default 32) caps the passes that may produce code. Reaching the cap is an error that names the metaprograms still producing code. Once expansion stops, the `let meta` items and operator declarations are removed, and Sema sees ordinary code. Sema defines types in dependency order, so a generated type may come after its uses.

## Tests

`tests/meta/*.pia` are lit tests:

| Test | Covers |
| --- | --- |
| `derive.pia` | `@derive(eq)` and record `=`/`<>`, proved; deferral until a later pass defines a type |
| `operators.pia` | a user operator's precedence, renaming and `[toplevel]` resolution |
| `errors.pia` | undeclared operators, unknown derives, failing metaprograms, operators for a type |
| `waiting.pia` | a derive waiting for a type that is never defined |
| `cycles.pia` | `--meta-cycles` and its default |
| `shadowing.pia`, `builtin_name.pia` | the no-shadowing rule, and that quote binders never trip it |
| `comments.pia` | where comments attach, and that quotes, splices, derives and operators keep them |
| `doc_lint.pia` | a metaprogram that walks `listing ()` and insists on doc comments |
| `generators.pia`, `generator_errors.pia` | the list and signature builtins, a generator that writes one proved case per combination of bounds, and their errors; `tests/std/test_gen.pia` proves what `Pia.Test.Gen` writes |
| `tactic_errors.pia` | `@by` on something other than a lemma, tactics that are not total or pure, and tactics that return something other than proof steps; `tests/verify/tactics.pia` proves what tactics write |
| `literate.pia.md`, `literate_errors.pia.md`, `literate_unclosed.pia.md` | a literate program, proved, and its errors |

## Not yet

- operators for a type, and overloading
- nested quotes
- a metaprogram's errors are reported at the expansion site, not inside the metaprogram
- concepts (`let meta Numeric (t : type) : concept`) and generic types
- module-level prelude import control
