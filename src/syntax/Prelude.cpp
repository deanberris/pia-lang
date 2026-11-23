// The prelude every Pia program imports (design.md, "Prelude"; ADR 0008).
//
// Operators exist only through these declarations: each one gives a symbol
// its fixity, which the parser reads, and an expansion to a core builtin,
// which the meta engine (src/meta) applies. The builtins are listed in
// docs/meta.md. The prelude's own code uses no infix operators outside
// quotes, so it parses before any operator is declared.

#include "syntax/Parser.h"

namespace pia::syntax {

std::string_view preludeSource() {
  static constexpr std::string_view source = R"pia(
(* Logic. These short-circuit in code and are plain logic in contracts. *)
let meta operator ( ==> ) : prec 1 right = let (a) (b) => `( implies $a $b )
let meta operator ( <==> ) : prec 1 right = let (a) (b) => `( iff $a $b )
let meta operator ( || ) : prec 2 right = let (a) (b) => `( or $a $b )
let meta operator ( && ) : prec 3 right = let (a) (b) => `( and $a $b )

(* Comparisons. *)
let meta operator ( = ) : prec 4 none = let (a) (b) => `( eq $a $b )
let meta operator ( <> ) : prec 4 none = let (a) (b) => `( ne $a $b )
let meta operator ( < ) : prec 4 none = let (a) (b) => `( lt $a $b )
let meta operator ( > ) : prec 4 none = let (a) (b) => `( gt $a $b )
let meta operator ( <= ) : prec 4 none = let (a) (b) => `( le $a $b )
let meta operator ( >= ) : prec 4 none = let (a) (b) => `( ge $a $b )

(* Arithmetic. `+|` and `-|` saturate whatever the overflow mode. *)
let meta operator ( + ) : prec 6 left = let (a) (b) => `( add $a $b )
let meta operator ( - ) : prec 6 left = let (a) (b) => `( sub $a $b )
let meta operator ( +| ) : prec 6 left = let (a) (b) => `( add_sat $a $b )
let meta operator ( -| ) : prec 6 left = let (a) (b) => `( sub_sat $a $b )
let meta operator ( * ) : prec 7 left = let (a) (b) => `( mul $a $b )
let meta operator ( / ) : prec 7 left = let (a) (b) => `( div $a $b )
let meta operator ( % ) : prec 7 left = let (a) (b) => `( rem $a $b )
let meta operator ( mod ) : prec 7 left = let (a) (b) => `( rem $a $b )

(* Bits, with C's symbols (docs/stdlib.md, group 2). Unlike C they bind
   tighter than comparisons, so `x & mask = 0` is `(x & mask) = 0`. `|` is
   bitwise or only inside brackets. `~x` is built in, like `-x`. *)
let meta operator ( << ) : prec 5.5 left = let (a) (b) => `( shl $a $b )
let meta operator ( >> ) : prec 5.5 left = let (a) (b) => `( shr $a $b )
let meta operator ( | ) : prec 6.3 left = let (a) (b) => `( bor $a $b )
let meta operator ( ^ ) : prec 6.4 left = let (a) (b) => `( bxor $a $b )
let meta operator ( & ) : prec 6.5 left = let (a) (b) => `( band $a $b )

(* The conjunction of a list of conditions, `true` when it is empty. *)
let meta fold_and (xs : list) : expr =
  fold (let (acc) (x) => `( $acc && $x )) `( true ) xs

(* @derive(eq): `eq_<t> (a : t) (b : t) : bool`, true when every field is
   equal. Its postcondition says so, so callers can reason about it. `=` on
   two values of a record type calls it. The function is documented, so
   hover and literate tools can say where it came from. *)
let meta derive_eq (t : type_decl) : item =
  let n = concat "eq_" (name t) in
  let c = fold_and (map (let (f) => `( $!a.$f = $!b.$f )) (fields t)) in
  let what = concat (name t) ", made by @derive(eq)." in
  with_doc (concat "Field-by-field equality for " what)
    `( let $n ($!a : $t) ($!b : $t) : bool ensures $!result <==> $c = $c )

(* @derive(json) (ADR 0045, step 2 to 4; docs/json.md): for a record of
   integers, range types and bools, `write_json_<t>` writes it as a JSON
   object with Pia.Text.Json.Write, into a caller's buffer with the room
   its precondition gives, and `read_json_<t>` reads one with
   Pia.Text.Json.Read and Pia.Text.Json.Lex. A member's name is its
   field's, or `@json(name = "...")` on the field, in printable ASCII.
   The reader finds a member by a decision tree built here, on the name's
   length, then on the first byte where the candidates differ, then one
   full compare; it keeps a flag per field, so a member given twice is
   `Duplicate_<t>` and one never given is `Missing_<t>`; an unknown one is
   `Unknown_<t>`; each integer's range is checked as its digits are read,
   `Range_<t>`; anything else is `Syntax_<t>`. Its error type,
   `<t>_json_error`, has exactly the constructors its type can raise.
   The value it returns is built only once every field is read, so it is
   fully initialised. The generated code calls those modules by their
   full paths, so a program that derives json imports their interfaces.
   It lives here until interfaces can export metaprograms (ADR 0039,
   step 3); then it moves to Pia.Text.Json.Derive. Names it binds end in
   `#field`, which no source can write. *)
let meta derive_json (t : type_decl) : list =
  let tn = name t in
  (* The modules' functions by their full paths, spliced as names. *)
  let json_write = let (f) => concat "Pia.Text.Json.Write." f in
  let json_read = let (f) => concat "Pia.Text.Json.Read." f in
  let fs = fields t in
  let nf = length fs in
  let idx = range nf in
  (* The member name of a field: @json(name = "...") or its own. *)
  let key_of = let (f) =>
    fold (let (acc) (a) =>
            if eq (nth a 0) "json" then
              fold (let (acc2) (arg) => if eq (nth arg 0) "name" then nth arg 1 else acc2) acc (nth a 1)
            else acc)
         f (field_attrs t f) in
  let keys = map key_of fs in
  let plain = let (k) =>
    fold (let (ok) (b) => and ok (and (ge b 32) (and (le b 126) (and (ne b 34) (ne b 92))))) (gt (length (bytes k)) 0) (bytes k) in
  let checked = map (let (k) => if plain k then k else fail (concat "@derive(json): the member name '" (concat k "' needs printable ASCII with no quote or backslash"))) keys in
  (* What a field is: "bool", or an integer with its bounds. *)
  let is_bool = let (f) =>
    let ft = field_type t f in if eq (kind ft) "TypeName" then eq (name ft) "bool" else false in
  (* Integer and range types have bounds; any other type is not supported
     yet, which is an error that names the field. *)
  let ints = [ "u8"; "u16"; "u32"; "u64"; "usize"; "i8"; "i16"; "i32"; "i64"; "isize" ] in
  let supported = map (let (f) =>
      let ft = field_type t f in
      if is_bool f then true
      else if eq (kind ft) "RangeType" then true
      else if eq (kind ft) "TypeName" then
        (if fold (let (h) (n) => or h (eq n (name ft))) false ints then true
         else fail (concat "@derive(json): the field '" (concat f "' has a type that @derive(json) cannot read or write yet; it takes integers, range types and bool")))
      else fail (concat "@derive(json): the field '" (concat f "' has a type that @derive(json) cannot read or write yet; it takes integers, range types and bool")))
    fs in
  let bounds = let (f) => range_of (field_type t f) in
  (* The writer of a field's value, and the room it needs. *)
  let writer = let (f) =>
    if is_bool f then [ "write_bool"; 5 ]
    else (
      let b = bounds f in
      let lo = nth b 0 in
      let hi = nth b 1 in
      if ge lo 0 then
        (if le hi 255 then [ "write_u8"; 3 ] else if le hi 65535 then [ "write_u16"; 5 ]
         else if le hi 4294967295 then [ "write_u32"; 10 ] else [ "write_u64"; 20 ])
      else
        (if and (ge lo (-128)) (le hi 127) then [ "write_i8"; 4 ] else if and (ge lo (-32768)) (le hi 32767) then [ "write_i16"; 6 ]
         else if and (ge lo (-2147483648)) (le hi 2147483647) then [ "write_i32"; 11 ] else [ "write_i64"; 20 ])) in
  (* A member's room: its key with quotes, the colon and its value. *)
  let member_room = let (i) => add (add (length (bytes (nth checked i))) 3) (nth (writer (nth fs i)) 1) in
  let room = fold (let (acc) (i) => add (add acc (member_room i)) (if lt (add i 1) nf then 1 else 0)) 2 idx in
  let wname = concat "write_json_" tn in
  let wfield = let (i) => concat (concat (concat "write_json_" tn) "_") (nth fs i) in
  (* One function per member: its key, a colon and its value. *)
  let member_writer = let (i) =>
    let f = nth fs i in
    let fn = wfield i in
    let ft = field_type t f in
    let kb = bytes (nth checked i) in
    let kn = length kb in
    let r = member_room i in
    let w = concat "Pia.Text.Json.Write." (nth (writer f) 0) in
    `( let $fn ($!dst : borrowed inout mutable [u8]) ($!pos : usize) ($!v : $ft) : usize
         requires $!pos <= len $!dst && len $!dst - $!pos >= $r
         ensures $!pos < $!result && $!result - $!pos <= $r
       = let $!key : [u8; $kn] = [ $kb ] in
         let $!p1 = $(json_write "write_key") $!dst $!pos $!key in
         let $!p2 = $(json_write "write_colon") $!dst $!p1 in
         $w $!dst $!p2 $!v ) in
  (* The object: `{`, the members with commas between, `}`. *)
  let body = fold (let (acc) (i) =>
      let fn = wfield i in
      let f = nth fs i in
      let after = if lt (add i 1) nf then `( $(json_write "write_comma") $!dst ($fn $!dst $acc $!v.$f) ) else `( $fn $!dst $acc $!v.$f ) in
      after)
    `( $(json_write "write_lbrace") $!dst $!pos ) idx in
  let writer_fn =
    `( let $wname ($!dst : borrowed inout mutable [u8]) ($!pos : usize) ($!v : $t) : usize
         requires $!pos <= len $!dst && len $!dst - $!pos >= $room
         ensures $!pos < $!result && $!result <= $!pos + $room
       = $(json_write "write_rbrace") $!dst ($body) ) in
  (* ---- The reader ---- *)
  let has_int = fold (let (acc) (f) => or acc (eq (is_bool f) false)) false fs in
  let ctor = let (c) => concat (concat c "_") tn in
  let esyn = ctor "Syntax" in
  let eunk = ctor "Unknown" in
  let edup = ctor "Duplicate" in
  let emis = ctor "Missing" in
  let erng = ctor "Range" in
  let ename = concat tn "_json_error" in
  (* The error set is exact: Range only when there is an integer field. *)
  let error_type =
    if has_int then
      `( let $ename = type | $esyn of usize | $eunk of usize | $edup of usize | $emis of usize | $erng of usize )
    else
      `( let $ename = type | $esyn of usize | $eunk of usize | $edup of usize | $emis of usize ) in
  let rname = concat tn "_json_read" in
  let read_type = `( let $rname = type { value : $t; stop : usize } ) in
  let fread = let (i) => concat (concat (concat "read_json_" tn) "_") (nth fs i) in
  let ftype = let (i) => concat (concat (concat tn "_") (nth fs i)) "_json" in
  (* One reader per field's value, with its range checked as it reads. *)
  let field_reader = let (i) =>
    let f = nth fs i in
    let fn = fread i in
    let rt = ftype i in
    let ft = field_type t f in
    let rtype = `( let $rt = type { value : $ft; stop : usize } ) in
    let body =
      if is_bool f then
        `( match $(json_read "read_bool") $!s $!pos with
           | Ok $!r -> Ok { value = $!r.value; stop = $!r.stop }
           | Err $!p -> Err ($esyn $!p) )
      else (
        let b = bounds f in
        let lo = nth b 0 in
        let hi = nth b 1 in
        if ge lo 0 then
          `( match $(json_read "read_uint") $!s $!pos $hi with
             | Ok $!r ->
                 if $!r.value < $lo then Err ($erng $!r.start)
                 else (let $!v : $ft = $!r.value in Ok { value = $!v; stop = $!r.stop })
             | Err $!e ->
                 (match $!e with
                  | NotNumber $!p -> Err ($esyn $!p)
                  | OutOfRange $!p -> Err ($erng $!p)) )
        else
          `( match $(json_read "read_int") $!s $!pos $lo $hi with
             | Ok $!r -> (let $!v : $ft = $!r.value in Ok { value = $!v; stop = $!r.stop })
             | Err $!e ->
                 (match $!e with
                  | NotNumber $!p -> Err ($esyn $!p)
                  | OutOfRange $!p -> Err ($erng $!p)) )) in
    [ rtype;
      `( let $fn ($!s : [u8]) ($!pos : usize) : result $rt $ename
           requires $!pos <= len $!s
           ensures (match $!result with
             | Ok $!q -> $!pos < $!q.stop && $!q.stop <= len $!s
             | Err _ -> true)
         = $body ) ] in
  (* The key decision tree: on the name's length, then on the first byte
     where the candidates differ, then one full compare. It returns the
     field's number from 1, or 0 for no field. *)
  let kbytes = map bytes checked in
  let dup_free = fold (let (acc) (i) =>
      fold (let (a2) (j) => if and (lt j i) (eq (nth checked j) (nth checked i)) then fail (concat "@derive(json): two fields have the member name " (nth checked i)) else a2) acc idx)
    true idx in
  let distinct = let (xs) => fold (let (acc) (x) => if fold (let (h) (y) => or h (eq y x)) false acc then acc else concat acc [ x ]) [] xs in
  let compare_all = let (c) =>
    let bs = nth c 1 in
    fold (let (acc) (j) => `( $acc && $!s.[$!a + $j] = $(nth bs j) )) `( true ) (range (length bs)) in
  let tree (cs : list) : expr =
    if eq (length cs) 1 then
      `( if $(compare_all (nth cs 0)) then $(add (nth (nth cs 0) 0) 1) else 0 )
    else (
      let n = length (nth (nth cs 0) 1) in
      let differs = let (p) => gt (length (distinct (map (let (c) => nth (nth c 1) p) cs))) 1 in
      let p = nth (filter differs (range n)) 0 in
      let vals = distinct (map (let (c) => nth (nth c 1) p) cs) in
      fold (let (acc) (v) =>
              let sub = filter (let (c) => eq (nth (nth c 1) p) v) cs in
              `( if $!s.[$!a + $p] = $v then $(tree sub) else $acc ))
           `( 0 ) vals) in
  let cands = map (let (i) => [ i; nth kbytes i ]) idx in
  let lens = distinct (map (let (c) => length (nth c 1)) cands) in
  let dispatch = fold (let (acc) (l) =>
      `( if $!n = $l then $(tree (filter (let (c) => eq (length (nth c 1)) l) cands)) else $acc ))
    `( 0 ) lens in
  let kname = concat "json_key_" tn in
  let key_fn =
    `( let $kname ($!s : [u8]) ($!a : usize) ($!n : usize) : u8
         requires $!a <= len $!s && $!n <= len $!s - $!a
         ensures $!result <= $nf
       = $dispatch ) in
  (* The reader: `{`, then members until `}`, each name once. *)
  let seen = let (i) => concat "seen#" (nth fs i) in
  let val = let (i) => concat "val#" (nth fs i) in
  (* A member's action: once, reading its value; a second time is an
     error. *)
  let action = let (i) =>
    let sn = seen i in
    let vn = val i in
    let fn = fread i in
    `( if $sn then ($!err <- $edup $!k.start; 0)
       else
         (match $fn $!s $!k.next with
          | Ok $!q -> ($vn <- $!q.value; $sn <- true; $!q.stop)
          | Err $!e -> ($!err <- $!e; 0)) ) in
  let actions = fold (let (acc) (i) =>
      `( if $!which = $(add i 1) then $(action i) else $acc ))
    `( ($!err <- $eunk $!k.start; 0) ) idx in
  let all_seen = fold (let (acc) (i) => `( $acc && $(seen i) )) `( true ) idx in
  let record = fold (let (acc) (i) => concat acc [ [ nth fs i; val i ] ]) [] idx in
  let loop =
    `( let $!at : mutable usize = $!o.next in
       let $!err : mutable $ename = $esyn $!pos in
       let $!going : mutable bool = $!o.empty = false in
       let $!ok : mutable bool = true in
       while $!going
         invariant $!pos < $!at && $!at <= len $!s
         decreases len $!s - $!at + (if $!going then 1 else 0)
       do
         match $(json_read "read_key") $!s $!at with
         | Err $!p -> ($!err <- $esyn $!p; $!ok <- false; $!going <- false)
         | Ok $!k ->
             let $!which = $kname $!s ($!k.start + 1) ($!k.stop - $!k.start - 2) in
             let $!next : usize = $actions in
             if $!next > $!at then
               (match $(json_read "after_member") $!s $!next with
                | Ok $!sp -> ($!at <- $!sp.next; $!going <- $!sp.more)
                | Err $!p -> ($!err <- $esyn $!p; $!ok <- false; $!going <- false))
             else ($!ok <- false; $!going <- false)
       done;
       if $!ok = false then Err $!err
       else if $all_seen then Ok { value = { $record }; stop = $!at }
       else Err ($emis $!at) ) in
  let wrapped = fold (let (acc) (i) =>
      let sn = seen i in
      let vn = val i in
      let ft = field_type t (nth fs i) in
      let init = if is_bool (nth fs i) then `( false ) else nth (bounds (nth fs i)) 0 in
      `( let $sn : mutable bool = false in let $vn : mutable $ft = $init in $acc ))
    loop (reverse idx) in
  let rfn = concat "read_json_" tn in
  let reader_fn =
    `( let $rfn ($!s : [u8]) ($!pos : usize) : result $rname $ename
         requires $!pos <= len $!s
         ensures (match $!result with
           | Ok $!r -> $!pos < $!r.stop && $!r.stop <= len $!s
           | Err _ -> true)
       = match $(json_read "open_object") $!s $!pos with
         | Err $!p -> Err ($esyn $!p)
         | Ok $!o -> $wrapped ) in
  concat (concat (map member_writer idx) [ writer_fn ])
    (concat [ error_type; read_type; key_fn ] (concat (fold (let (acc) (i) => concat acc (field_reader i)) [] idx) [ reader_fn ]))

(* State machines as theories (ADR 0036, step 5; docs/theories.md).
   `let theory Conn = machine "conn" conn_state Closed [ edge Closed
   "connect" Open; ... ]` builds a theory with a sort `conn`, `at c : conn
   -> conn_state`, a `start` at the initial state, and for each event `e`
   an abstract function `e`, a predicate `allowed_e` that holds exactly in
   the states with an `e` edge, and one axiom per edge saying where it
   leads; and a model `<sort>_states` in which a value of the sort is its
   state. The
   model proves every axiom, so nothing is trusted. Binders are named
   `c#machine`, which no source can write, and member names are kept. It
   uses only map and fold, so it is total. *)
(* One transition: in state `from`, `event` leads to `to`. *)
let meta edge (from : expr) (event : string) (to : expr) : expr =
  let (k) => k from event to

let meta machine (sort : string) (states : type_decl) (start : expr) (edges : list) : list =
  let ev_of = let (e) => e (let (f) (ev) (t) => ev) in
  let from_of = let (e) => e (let (f) (ev) (t) => f) in
  let to_of = let (e) => e (let (f) (ev) (t) => t) in
  let has = let (xs) (x) => fold (let (acc) (y) => acc || y = x) false xs in
  let events = fold (let (acc) (e) => if has acc (ev_of e) then acc else concat acc [ev_of e]) [] edges in
  let of_event = let (ev) => fold (let (acc) (e) => if ev_of e = ev then concat acc [e] else acc) [] edges in
  let x = "c#machine" in
  let allowed = let (ev) => concat "allowed_" ev in
  let cond = let (ev) => fold (let (acc) (e) => `( $acc || at $x = $(from_of e) )) `( false ) (of_event ev) in
  let mcond = let (ev) => fold (let (acc) (e) => `( $acc || $x = $(from_of e) )) `( false ) (of_event ev) in
  let step = let (ev) => fold (let (acc) (e) => `( if $x = $(from_of e) then $(to_of e) else $acc )) `( $x ) (of_event ev) in
  let per_event = let (ev) =>
    let a = allowed ev in
    let an = concat ev "_allowed" in
    concat [ `( let spec $ev : (c : $sort) -> $sort )
           ; `( let spec $a : (c : $sort) -> bool )
           ; `( let axiom $an ($x : $sort) ensures $a $x = $(cond ev) ) ]
           (map (let (e) =>
                   let n = concat ev (concat "_from_" (name (from_of e))) in
                   `( let axiom $n ($x : $sort) requires at $x = $(from_of e) ensures at ($ev $x) = $(to_of e) ))
                (of_event ev)) in
  let members = fold (let (acc) (ev) => concat acc (per_event ev))
    [ `( let sort $sort )
    ; `( let spec at : (c : $sort) -> $states )
    ; `( let spec start : $sort )
    ; `( let axiom start_at ensures at start = $start ) ]
    events in
  let model_event = let (ev) =>
    let a = allowed ev in
    [ `( let spec $ev ($x : $states) : $states = $(step ev) )
    ; `( let spec $a ($x : $states) : bool = $(mcond ev) ) ] in
  let model = fold (let (acc) (ev) => concat acc (model_event ev))
    [ `( let sort $sort = $states )
    ; `( let spec at ($x : $states) : $states = $x )
    ; `( let spec start : $states = $start ) ]
    events in
  let mname = concat sort "_states" in
  [ `( let theory machine_theory = sig $members end )
  ; `( let model $mname : machine_theory = struct $model end ) ]
(* Litmus tests (ADR 0052, section 4). `litmus "mp" [thread [...]; ...]
   "forbidden" [is "r1" 1; ...]` is a lemma about every consistent RC11
   execution of the threads: "forbidden" and "allowed" claim that no
   execution ends with the outcome, so a forbidden outcome is proved and an
   allowed one fails with a counterexample, which is a witness execution;
   "race" claims that no execution has a data race. The events of the
   test are finite, so each relation is a matrix of booleans, each derived
   relation is given by its lower bounds, and each acyclicity is a rank
   (docs/theories.md). Orders are strings, as in `store "release" "x" 1`. *)
let meta check_order (what : string) (o : string) (allowed : list) : string =
  if fold (let (acc) (x) => acc || x = o) false allowed then o
  else fail (concat "a litmus " (concat what (concat " takes no order " o)))
let meta write (loc : string) (v : int) : expr = let (k) => k "W" "na" loc v "" ""
let meta read (loc : string) (reg : string) : expr = let (k) => k "R" "na" loc 0 reg ""
let meta store (o : string) (loc : string) (v : int) : expr =
  let o' = check_order "store" o ["relaxed"; "release"; "seq_cst"] in
  let (k) => k "W" o' loc v "" ""
let meta load (o : string) (loc : string) (reg : string) : expr =
  let o' = check_order "load" o ["relaxed"; "acquire"; "seq_cst"] in
  let (k) => k "R" o' loc 0 reg ""
let meta swap (o : string) (loc : string) (v : int) (reg : string) : expr =
  let o' = check_order "swap" o ["relaxed"; "acquire"; "release"; "acq_rel"; "seq_cst"] in
  let (k) => k "U" o' loc v reg "swap"
let meta fetch_add (o : string) (loc : string) (v : int) (reg : string) : expr =
  let o' = check_order "fetch_add" o ["relaxed"; "acquire"; "release"; "acq_rel"; "seq_cst"] in
  let (k) => k "U" o' loc v reg "add"
let meta barrier (o : string) : expr =
  let o' = check_order "barrier" o ["acquire"; "release"; "acq_rel"; "seq_cst"] in
  let (k) => k "F" o' "" 0 "" ""
let meta thread (ops : list) : list = ops
let meta is (reg : string) (v : int) : expr = let (k) => k "reg" reg v
let meta final (loc : string) (v : int) : expr = let (k) => k "final" loc v

let meta litmus (name : string) (threads : list) (verdict : string) (conds : list) : item =
  (* An event: index, thread, kind (R, W or F), order, location, the value
     a write stores, the register a read fills, the op of a
     read-modify-write's write, and the index of its read. *)
  let ev (i : int) (t : int) (kd : string) (o : string) (l : string) (v : int) (r : string) (op : string) (p : int) : expr =
    let (k) => k i t kd o l v r op p in
  let ix = let (e) => e (let (i) (t) (kd) (o) (l) (v) (r) (op) (p) => i) in
  let th = let (e) => e (let (i) (t) (kd) (o) (l) (v) (r) (op) (p) => t) in
  let kind = let (e) => e (let (i) (t) (kd) (o) (l) (v) (r) (op) (p) => kd) in
  let ord = let (e) => e (let (i) (t) (kd) (o) (l) (v) (r) (op) (p) => o) in
  let loc = let (e) => e (let (i) (t) (kd) (o) (l) (v) (r) (op) (p) => l) in
  let cv = let (e) => e (let (i) (t) (kd) (o) (l) (v) (r) (op) (p) => v) in
  let reg = let (e) => e (let (i) (t) (kd) (o) (l) (v) (r) (op) (p) => r) in
  let rop = let (e) => e (let (i) (t) (kd) (o) (l) (v) (r) (op) (p) => op) in
  let partner = let (e) => e (let (i) (t) (kd) (o) (l) (v) (r) (op) (p) => p) in
  let okind = let (a) => a (let (kd) (o) (l) (v) (r) (op) => kd) in
  let oord = let (a) => a (let (kd) (o) (l) (v) (r) (op) => o) in
  let oloc = let (a) => a (let (kd) (o) (l) (v) (r) (op) => l) in
  let oval = let (a) => a (let (kd) (o) (l) (v) (r) (op) => v) in
  let oreg = let (a) => a (let (kd) (o) (l) (v) (r) (op) => r) in
  let oop = let (a) => a (let (kd) (o) (l) (v) (r) (op) => op) in
  let has = let (xs) (x) => fold (let (acc) (y) => acc || y = x) false xs in
  let all_ops = fold (let (acc) (t) => concat acc t) [] threads in
  let locs = fold (let (acc) (a) => if okind a = "F" || has acc (oloc a) then acc else concat acc [oloc a]) [] all_ops in
  let inits = fold (let (acc) (l) => concat acc [ev (length acc) (0 - 1) "W" "na" l 0 "" "" (0 - 1)]) [] locs in
  (* Each thread's ops in order; a read-modify-write is a read and then a
     write, linked as partners. *)
  let add_thread = let (st) (t) =>
    let tid = fold (let (acc) (e) => if th e + 1 > acc then th e + 1 else acc) 0 st in
    fold (let (acc) (a) =>
      let i = length acc in
      if okind a = "U" then
        concat acc [ ev i tid "R" (oord a) (oloc a) 0 (oreg a) "" (0 - 1)
                   ; ev (i + 1) tid "W" (oord a) (oloc a) (oval a) "" (oop a) i ]
      else concat acc [ev i tid (okind a) (oord a) (oloc a) (oval a) (oreg a) "" (0 - 1)])
      st t in
  let evs = fold add_thread inits threads in
  let n = length evs in
  let nn = n * n in
  let p = let (a) (b) => ix a * n + ix b in
  let isw = let (e) => kind e = "W" in
  let isr = let (e) => kind e = "R" in
  let isf = let (e) => kind e = "F" in
  let atomic = let (e) => ord e <> "na" in
  let rel = let (e) => ord e = "release" || ord e = "acq_rel" || ord e = "seq_cst" in
  let acq = let (e) => ord e = "acquire" || ord e = "acq_rel" || ord e = "seq_cst" in
  let sc = let (e) => ord e = "seq_cst" in
  let init = let (e) => th e < 0 in
  let same = let (a) (b) => ix a = ix b in
  let po = let (a) (b) => th a = th b && th a >= 0 && ix a < ix b in
  let sloc = let (a) (b) => isf a = false && isf b = false && loc a = loc b in
  let rmw = let (r) (w) => isw w && partner w = ix r in
  let cand = let (w) (r) => isw w && isr r && sloc w r in
  let pairs = fold (let (acc) (a) => concat acc (map (let (b) => let (k) => k a b) evs)) [] evs in
  let pa = let (q) => q (let (a) (b) => a) in
  let pb = let (q) => q (let (a) (b) => b) in
  let each = let (f) => fold (let (acc) (q) => concat acc (f (pa q) (pb q))) [] pairs in
  let each_ev = let (f) => fold (let (acc) (e) => concat acc (f e)) [] evs in
  let rf = let (w) (r) => `( $!rf.[$(p w r)] ) in
  let hb = let (a) (b) => `( $!hb.[$(p a b)] ) in
  let eco = let (a) (b) => `( $!eco.[$(p a b)] ) in
  let mo = let (a) (b) => `( $!mo.[$(ix a)] < $!mo.[$(ix b)] ) in
  let any = let (xs) => fold (let (acc) (x) => `( $acc || $x )) `( false ) xs in
  let fr = let (r) (w) => any (fold (let (acc) (w0) => if cand w0 r && same w0 w = false then concat acc [ `( $(rf w0 r) && $(mo w0 w) ) ] else acc) [] evs) in
  let frs = let (r) (w) => if isr r && isw w && sloc r w then [fr r w] else [] in
  (* reads-from: each read reads exactly one write to its location, and
     gets its value. *)
  let c_rf = each_ev (let (r) =>
    if isr r = false then [] else (
      let ws = fold (let (acc) (w) => if cand w r then concat acc [w] else acc) [] evs in
      concat [any (map (let (w) => rf w r) ws)]
        (concat (map (let (w) => `( $(rf w r) ==> $!v.[$(ix r)] = $!v.[$(ix w)] )) ws)
                (each (let (w1) (w2) => if cand w1 r && cand w2 r && ix w1 < ix w2 then [ `( ($(rf w1 r) && $(rf w2 r)) = false ) ] else []))))) in
  (* The values writes store. *)
  let c_val = each_ev (let (w) =>
    if isw w = false then [] else
    if rop w = "add" then [ `( $!v.[$(ix w)] = $!v.[$(partner w)] + $(cv w) ) ]
    else [ `( $!v.[$(ix w)] = $(cv w) ) ]) in
  (* The modification order: a rank per write, distinct per location, the
     initial write first. *)
  let c_mo = each (let (a) (b) =>
    if isw a && isw b && sloc a b && ix a < ix b then
      (if init a then [ mo a b ] else [ `( $!mo.[$(ix a)] <> $!mo.[$(ix b)] ) ])
    else []) in
  (* Release sequences, lower bounds: rs w x when x continues w's. *)
  let c_rs = concat
    (each (let (w) (x) =>
       if isw w && isw x && sloc w x && atomic x && (same w x || po w x) then [ `( $!rs.[$(p w x)] ) ] else []))
    (each (let (w) (x) =>
       if isw w = false || isw x = false || sloc w x = false then [] else
       each (let (r) (y) => if rmw r y && cand x r && sloc w r then [ `( $!rs.[$(p w x)] && $(rf x r) ==> $!rs.[$(p w y)] ) ] else []))) in
  (* Happens-before, lower bounds: program order, the initial writes, sw,
     and transitivity. *)
  let relpre = let (a) (w) => isw w && atomic w && ((same a w && rel a) || (isf a && rel a && po a w)) in
  let acqpost = let (r) (b) => isr r && atomic r && ((same r b && acq b) || (isf b && acq b && po r b)) in
  let c_sw = each (let (a) (w) =>
    if relpre a w = false then [] else
    each (let (r) (b) =>
      if acqpost r b = false || same a b then [] else
      fold (let (acc) (x) => if cand x r && sloc x w then concat acc [ `( $!rs.[$(p w x)] && $(rf x r) ==> $(hb a b) ) ] else acc) [] evs)) in
  let c_hb = concat
    (each (let (a) (b) => if po a b || (init a && init b = false) then [ hb a b ] else []))
    (each (let (a) (b) =>
       if same a b then [] else
       fold (let (acc) (c) => if same a c || same b c then acc else concat acc [ `( $(hb a b) && $(hb b c) ==> $(hb a c) ) ]) [] evs)) in
  (* The extended coherence order, lower bounds, per location. *)
  let c_eco = concat
    (each (let (a) (b) =>
       if sloc a b = false || same a b then [] else
       concat (if cand a b then [ `( $(rf a b) ==> $(eco a b) ) ] else [])
       (concat (if isw a && isw b then [ `( $(mo a b) ==> $(eco a b) ) ] else [])
               (map (let (f) => `( $f ==> $(eco a b) )) (frs a b)))))
    (each (let (a) (b) =>
       if sloc a b = false || same a b then [] else
       fold (let (acc) (c) => if sloc a c && same a c = false && same b c = false then concat acc [ `( $(eco a b) && $(eco b c) ==> $(eco a c) ) ] else acc) [] evs)) in
  (* Coherence: hb ; eco? is irreflexive. *)
  let c_coh = concat
    (each_ev (let (a) => [ `( $(hb a a) = false ) ]))
    (each (let (a) (b) => if sloc a b && same a b = false then [ `( ($(hb a b) && $(eco b a)) = false ) ] else [])) in
  (* Atomicity: nothing comes between a read-modify-write's read and its
     write in the modification order. *)
  let c_atom = each (let (r) (w) =>
    if rmw r w = false then [] else
    fold (let (acc) (x) => if isw x && sloc x w && same x w = false then concat acc [ `( ($(fr r x) && $(mo x w)) = false ) ] else acc) [] evs) in
  (* No thin air: po ∪ rf is acyclic, by a rank. *)
  let c_air = concat
    (each (let (a) (b) => if po a b then [ `( $!air.[$(ix a)] < $!air.[$(ix b)] ) ] else []))
    (each (let (w) (r) => if cand w r then [ `( $(rf w r) ==> $!air.[$(ix w)] < $!air.[$(ix r)] ) ] else [])) in
  (* SC: psc is acyclic, by a rank. *)
  let scb = let (a) (b) => `( $!scb.[$(p a b)] ) in
  let lsc = let (a) (b) => `( $!lsc.[$(p a b)] ) in
  let sco = let (a) (b) => `( $!sco.[$(ix a)] < $!sco.[$(ix b)] ) in
  let any_sc = fold (let (acc) (e) => acc || sc e) false evs in
  let c_sc = if any_sc = false then [] else concat
    (each (let (a) (b) =>
      if same a b then [] else
      concat (if po a b then [ scb a b ] else [])
      (concat (if sloc a b then [ `( $(hb a b) ==> $(scb a b) ) ] else [])
      (concat (if isw a && isw b && sloc a b then [ `( $(mo a b) ==> $(scb a b) ) ] else [])
      (concat (map (let (f) => `( $f ==> $(scb a b) )) (frs a b))
              (each (let (c) (d) => if po a c && sloc a c = false && po d b && sloc d b = false && same c d = false then [ `( $(hb c d) ==> $(scb a b) ) ] else []))))))) 
    (concat
      (each (let (a) (y) =>
        if sc a = false then [] else
        concat [ `( $(scb a y) ==> $(lsc a y) ) ]
          (if isf a then fold (let (acc) (x) => if same a x then acc else concat acc [ `( $(hb a x) && $(scb x y) ==> $(lsc a y) ) ]) [] evs else [])))
      (each (let (a) (b) =>
        if sc a = false || sc b = false || same a b then [] else
        concat [ `( $(lsc a b) ==> $(sco a b) ) ]
          (concat (if isf b then fold (let (acc) (y) => if same y b then acc else concat acc [ `( $(lsc a y) && $(hb y b) ==> $(sco a b) ) ]) [] evs else [])
          (if isf a && isf b then concat [ `( $(hb a b) ==> $(sco a b) ) ]
             (each (let (x) (y) => if sloc x y && same x y = false then [ `( $(hb a x) && $(eco x y) && $(hb y b) ==> $(sco a b) ) ] else []))
           else []))))) in
  (* Registers hold what their reads read. *)
  let regs = fold (let (acc) (e) => if isr e && reg e <> "" then concat acc [e] else acc) [] evs in
  let c_reg = map (let (e) => `( $(reg e) = $!v.[$(ix e)] )) regs in
  let params = map (let (e) => param (reg e) "int") regs in
  let conj = let (xs) => fold (let (acc) (x) => `( $acc && $x )) `( true ) xs in
  let ckind = let (c) => c (let (kd) (a) (b) => kd) in
  let cname = let (c) => c (let (kd) (a) (b) => a) in
  let cval = let (c) => c (let (kd) (a) (b) => b) in
  let last = let (l) (w) => fold (let (acc) (x) => if isw x && loc x = l && same x w = false then `( $acc && $(mo x w) ) else acc) `( true ) evs in
  (* Each location an outcome names gets `<loc>_final`, the value of its
     last write in mo, so a witness shows it. *)
  let finals = fold (let (acc) (c) => if ckind c = "final" && has acc (cname c) = false then concat acc [cname c] else acc) [] conds in
  let fname = let (l) => concat l "_final" in
  let c_final = map (let (l) => any (fold (let (acc) (w) => if isw w && loc w = l then concat acc [ `( $(last l w) && $!v.[$(ix w)] = $(fname l) ) ] else acc) [] evs)) finals in
  let cond = let (c) =>
    if ckind c = "reg" then `( $(cname c) = $(cval c) )
    else `( $(fname (cname c)) = $(cval c) ) in
  let outcome = conj (map cond conds) in
  let params' = concat params (map (let (l) => param (fname l) "int") finals) in
  let all = fold concat [] [c_rf; c_val; c_mo; c_rs; c_sw; c_hb; c_eco; c_coh; c_atom; c_air; c_sc; c_reg; c_final] in
  let racy = any (each (let (a) (b) =>
    if sloc a b && ix a < ix b && init a = false && init b = false && (isw a || isw b) && (atomic a = false || atomic b = false)
    then [ `( ($(hb a b) || $(hb b a)) = false ) ] else [])) in
  let goal = if verdict = "race" then racy else outcome in
  let consistent = conj all in
  with_doc (concat "Litmus test " (concat name (concat ": " verdict)))
    `( let lemma $name ($!rf : [bool; $nn]) ($!hb : [bool; $nn]) ($!eco : [bool; $nn])
           ($!rs : [bool; $nn]) ($!scb : [bool; $nn]) ($!lsc : [bool; $nn])
           ($!v : [int; $n]) ($!mo : [int; $n]) ($!air : [int; $n]) ($!sco : [int; $n]) $params' : unit
         requires $consistent
         ensures $goal ==> false
       = () )
)pia";
  return source;
}

}  // namespace pia::syntax
