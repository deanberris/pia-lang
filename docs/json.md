# JSON

`Pia.Text.Json` reads and writes JSON with every step proved against one grammar, RFC 8259's, stated as spec functions in `Pia.Text.Json.Spec` ([ADR 0045](adr/0045-json-derived-codecs-and-conforming-dom.md)). There are two ways in:

- **Straight into a type.** `@derive(json)` writes a reader and a writer for a record or a variant, and `Json.read<t>` reads a whole text as a `t`, with an error type that has exactly the errors `t` can raise.
- **Through a document.** `Pia.Text.Json.Dom.parse` reads any JSON text into a `json` value, a recursive type over the text, proved `valid_dom`. `@derive(json, json_dom)` then says when a document has a type's shape, and converts it, with no failure path left once it does.

Every example on this page is proved by `piac`.

## Building against the library

A program that uses the library imports its modules' interfaces, so it is proved against their contracts alone. `piac --emit=interface` writes each one as an artifact, here into the current directory:

```console
$ piac --emit=interface -o . lib/Pia/Text/Json/Spec.pia
```

```console
$ piac --emit=interface -o . lib/Pia/Text/Json/Lex.pia
```

```console
$ piac --emit=interface -o . lib/Pia/Text/Json/Read.pia
```

```console
$ piac --emit=interface -o . lib/Pia/Text/Json/Write.pia
```

```console
$ piac --emit=interface -o . lib/Pia/Text/Json/Derive.pia
```

```console
$ piac --emit=interface -o . lib/Pia/Mem/Alloc.pia
```

```console
$ piac --emit=interface -o . lib/Pia/Text/Json/Dom.pia
```

```console
$ piac --emit=interface -o . lib/Pia/Text/Json/Shape.pia
```

and `--iface-path=.` finds them.

## `@derive(json)`: a type's own codec

`@derive(json)` on a record of integers, range types and bools writes `write_json_<t>`, which writes a value into a buffer with the room its precondition states, and `read_json_<t>`, which reads one. A member's name is its field's, or `@json(name = "...")`. `Json.read<t>` reads a whole text, and its errors are `Json.json_errors t`: for `point` below, a syntax error, an unknown, duplicate or missing member, or a number out of its field's range, each at the position it was found.

<!-- example: point.pia -->
<!-- flags: --iface-path=. -->
```ocaml
import Pia.Text.Json.Spec.Grammar
import Pia.Text.Json.Lex.Lexer
import Pia.Text.Json.Read.Reader
import Pia.Text.Json.Write.Writer
import Pia.Text.Json.Derive.Derive as Json

let point = type { x : i32 @json(name = "xx"); y : u8; ok : bool } @derive(json)

(* The y of the point the text is, or 0. *)
let y_of (s : [u8]) : u8 =
  match Json.read<point> s with
  | Ok p -> p.y
  | Err _ -> 0

(* Why a text is not a point. *)
let why (e : Json.json_errors point) : u8 =
  match e with
  | Syntax_point _ -> 1 | Unknown_point _ -> 2 | Duplicate_point _ -> 3
  | Missing_point _ -> 4 | Range_point _ -> 5
```

The reader checks each integer's range as it reads its digits, so `"y": 256` stops at the third digit, and it never reads outside the text. Every goal of the derived code is proved where it is derived:

```console
$ piac --verify --iface-path=. point.pia
...
65 proved, 0 failed, 0 skipped
```

## The document: `Pia.Text.Json.Dom`

`json` is a recursive type ([recursive types](tour.md#recursive-types)) whose numbers and strings are spans of the text they were read from, so parsing copies nothing:

<!-- untested: an excerpt of lib/Pia/Text/Json/Dom.pia, which tests/std/json_dom.pia proves -->
```ocaml
let rec json = let (r : region) => type
  | JNull
  | Bool of bool
  | Num of span
  | Str of span
  | Arr of vec (json r) r
  | Obj of vec (member r) r
let rec member = let (r : region) => type { key : span; value : json r }
```

`Dom.parse s max_depth values members` reads all of `s` as one document, nested at most `max_depth` deep, taking each array from `values` and each object from `members`: two bump allocators over memory the caller lends. Each container is counted before it is read, so it takes one allocation of exactly its length. Its errors are a lex error, a misplaced token, too deep, trailing input and no memory, each with its position; a document it returns is `valid_dom s v`, every number, string and key a token of its kind.

A walk over a document is structural recursion, which needs no measure:

<!-- example: count.pia -->
<!-- flags: --iface-path=. -->
```ocaml
import Pia.Text.Json.Spec.Grammar
import Pia.Text.Json.Lex.Lexer
import Pia.Mem.Alloc.Allocators
import Pia.Text.Json.Dom.Document

(* The values in v, itself included, capped at a million. *)
let rec nodes (r : region) (v : Pia.Text.Json.Dom.json r) : int{0..1000000} =
  match v with
  | Arr a ->
    let total : mutable int{0..1000000} = 1 in
    for i in 0 .. len a.items do
      (let n = nodes a.items.[i] in
       total <- if n <= 1000000 - total then total + n else 1000000)
    done;
    total
  | Obj o ->
    let total : mutable int{0..1000000} = 1 in
    for i in 0 .. len o.items do
      (let n = nodes o.items.[i].value in
       total <- if n <= 1000000 - total then total + n else 1000000)
    done;
    total
  | _ -> 1

(* The values in the text, or 0 if it is not one document. *)
let count (s : [u8]) (cells : borrowed mutable [Pia.Text.Json.Dom.json]) (mems : borrowed mutable [Pia.Text.Json.Dom.member]) : int{0..1000000} =
  let vs : mutable Pia.Mem.Alloc.bump Pia.Text.Json.Dom.json = { mem = cells; used = 0 } in
  let ms : mutable Pia.Mem.Alloc.bump Pia.Text.Json.Dom.member = { mem = mems; used = 0 } in
  match Pia.Text.Json.Dom.parse s 16 vs ms with
  | Ok v -> nodes v
  | Err _ -> 0
```

```console
$ piac --verify --iface-path=. count.pia
...
8 proved, 0 failed, 0 skipped
```

## A document's shape: `@derive(json, json_dom)`

`@derive(json_dom)`, from `Pia.Text.Json.Shape`, says when a document has a record's shape, and converts it. It sits beside `@derive(json)`, whose member names it shares and whose writer `to_dom` uses, so that `@derive(json)` alone needs no document. For a record `t` of integers, range types and bools, and options and fixed arrays of them, it writes:

| Function | What it does |
| --- | --- |
| `conforms_json_<t> s v` | a spec function: v is an object with exactly one member for each field, each called its name, each value a number in its field's range or a bool as its field is, and no other member. An option field's member may be missing or `null`, both None, and an `[e; n]` field's is an array of exactly n values of e |
| `check_json_<t> s v` | decides it: `ensures result = conforms_json_<t> s v` |
| `from_dom_json_<t> s v` | `requires conforms_json_<t> s v`: the record, with no failure path, each field its member's value |
| `to_dom_json_<t> x text values members` | the document of x, written into text: `Ok v` is valid and conforms |

A number conforms to an integer field when it has only digits after an optional minus, and its value is in the field's range: `1.5` and `1e2` are not integers, as for the streaming reader. So reading a point from a document is a check and a conversion, and the conversion cannot fail:

<!-- example: shape.pia -->
<!-- flags: --iface-path=. -->
```ocaml
import Pia.Text.Json.Spec.Grammar
import Pia.Text.Json.Lex.Lexer
import Pia.Text.Json.Read.Reader
import Pia.Text.Json.Write.Writer
import Pia.Text.Json.Derive.Derive as Json
import Pia.Mem.Alloc.Allocators
import Pia.Text.Json.Dom.Document
import Pia.Text.Json.Shape.Shapes

let point = type { x : i32 @json(name = "xx"); y : u8; ok : bool } @derive(json, json_dom)

(* The point a document is, or that it is not one. *)
let get (s : [u8]) (v : Pia.Text.Json.Dom.json) : result point Pia.Text.Json.Shape.nonconforming =
  if check_json_point s v then Ok (from_dom_json_point s v) else Err Nonconforming
```

Every goal of the derived checks and conversions is proved where they are derived:

```console
$ piac --verify --iface-path=. shape.pia
...
102 proved, 0 failed, 0 skipped
```

`to_dom` writes its value with `@derive(json)`'s writer, parses the text back and checks it, so the document it returns is proved valid and conforming. That the writer's text always parses and conforms, so that its `Unparsed` and `Unconforming` errors never happen, is not proved yet. Nested record fields, variants and recursive user types come next ([ADR 0045](adr/0045-json-derived-codecs-and-conforming-dom.md), steps 5, 7 and 8).
