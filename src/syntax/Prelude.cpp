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
)pia";
  return source;
}

}  // namespace pia::syntax
