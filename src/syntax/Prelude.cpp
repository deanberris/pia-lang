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
