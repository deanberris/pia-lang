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
  (* An `option t` field holds a t or nothing (ADR 0045, step 5): its
     value's type is t, and the rest of the derive works on that. *)
  let is_opt = let (f) =>
    let ft = field_type t f in
    if eq (kind ft) "TypeApp" then
      (let h = name (nth (children ft) 0) in or (eq h "option") (eq h "Pia.Core.Option.option"))
    else false in
  let base = let (f) => if is_opt f then nth (children (field_type t f)) 1 else field_type t f in
  (* What a field's value is: "bool", or an integer with its bounds. *)
  let is_bool = let (f) =>
    let ft = base f in if eq (kind ft) "TypeName" then eq (name ft) "bool" else false in
  (* Integer and range types have bounds; any other type is not supported
     yet, which is an error that names the field. *)
  let ints = [ "u8"; "u16"; "u32"; "u64"; "usize"; "i8"; "i16"; "i32"; "i64"; "isize" ] in
  let supported = map (let (f) =>
      let ft = base f in
      if is_bool f then true
      else if eq (kind ft) "RangeType" then true
      else if eq (kind ft) "TypeName" then
        (if fold (let (h) (n) => or h (eq n (name ft))) false ints then true
         else fail (concat "@derive(json): the field '" (concat f "' has a type that @derive(json) cannot read or write yet; it takes integers, range types, bool and an option of one")))
      else fail (concat "@derive(json): the field '" (concat f "' has a type that @derive(json) cannot read or write yet; it takes integers, range types, bool and an option of one")))
    fs in
  let bounds = let (f) => range_of (base f) in
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
  (* None writes `null`, four bytes. *)
  let value_room = let (f) =>
    let r = nth (writer f) 1 in if and (is_opt f) (lt r 4) then 4 else r in
  let member_room = let (i) => add (add (length (bytes (nth checked i))) 3) (value_room (nth fs i)) in
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
         $(if is_opt f then
             `( match $!v with
                | $!None -> $(json_write "write_null") $!dst $!p2
                | Some $!x -> $w $!dst $!p2 $!x )
           else `( $w $!dst $!p2 $!v )) ) in
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
    let opt = is_opt f in
    let fn = if opt then concat (fread i) "_value" else fread i in
    let rt = if opt then concat (ftype i) "_value" else ftype i in
    let ft = base f in
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
    concat [ rtype;
      `( let $fn ($!s : [u8]) ($!pos : usize) : result $rt $ename
           requires $!pos <= len $!s
           ensures (match $!result with
             | Ok $!q -> $!pos < $!q.stop && $!q.stop <= len $!s
             | Err _ -> true)
         = $body ) ]
      (if opt then (
         (* `null` is None; anything else is the value, as Some. *)
         let ofn = fread i in
         let ort = ftype i in
         let full = field_type t f in
         [ `( let $ort = type { value : $full; stop : usize } );
           `( let $ofn ($!s : [u8]) ($!pos : usize) : result $ort $ename
                requires $!pos <= len $!s
                ensures (match $!result with
                  | Ok $!q -> $!pos < $!q.stop && $!q.stop <= len $!s
                  | Err _ -> true)
              = match $(json_read "read_null") $!s $!pos with
                | Ok $!e -> Ok { value = None; stop = $!e }
                | Err _ ->
                    (match $fn $!s $!pos with
                     | Ok $!r -> Ok { value = Some $!r.value; stop = $!r.stop }
                     | Err $!e -> Err $!e) ) ])
       else []) in
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
  (* A missing option member is None, so only the others must be seen. *)
  let all_seen = fold (let (acc) (i) => if is_opt (nth fs i) then acc else `( $acc && $(seen i) )) `( true ) idx in
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
      let init = if is_opt (nth fs i) then `( None )
                 else if is_bool (nth fs i) then `( false ) else nth (bounds (nth fs i)) 0 in
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
)pia";
  return source;
}

}  // namespace pia::syntax
