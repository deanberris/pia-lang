#ifndef PIA_IRGEN_BOXES_H
#define PIA_IRGEN_BOXES_H

#include <map>
#include <string>
#include <vector>
#include <string_view>

#include "syntax/Diagnostics.h"
#include "syntax/Syntax.h"

namespace pia::irgen {

// Whether `program` uses a concept in type position (ADR 0046, section 2),
// so that expandErasedBoxes has something to do.
bool hasErasedBoxes(const syntax::Node &program);

// A box over a concept, `box Shape r` (ADR 0046, steps 2 to 4), for the
// verifier. A type function whose first parameter is `@unsized`, such as
// `let box = let (@unsized t : type) (r : region) => type { ... }`, takes a
// concept C there, and `box C` is then its own type, `box_C`: one cache
// line of `words` 64-bit words (the cache-line amendment), the first the
// address of the boxed type's descriptor, the rest the object in its C
// layout. What the object is, the verifier knows only through C: each
// requirement `r` with one receiver of C's type is an uninterpreted
// function `erased_C.r_of` of the box, its contract an axiom of it, and
// each law of C over one value an axiom too, in the theory `erased_C`.
// Those axioms hold because `widen` runs the use check: every type it
// boxes meets C, contracts and laws included. So
//
// - `widen b`, for a full `box t` with t meeting C, makes a `box_C`, by
//   `erased_C_pack_t`, whose body is a `pia.box_pack`;
// - `r b` calls the requirement through the box, `erased_C_call_r`, whose
//   body is a `pia.box_call` through the descriptor: its precondition is a
//   goal at the call, and its result is, to the verifier,
//   `erased_C.r_of b`, about which the contract and laws say what they
//   say;
// - each type's `erased_C_thunk_r_t` calls `r` on a value of that type,
//   and codegen makes the descriptor's entries from them;
// - the call functions are `box_C`'s instance of C, so `box C` meets C and
//   generic code instantiates at it.
//
// A requirement whose receiver is not the only value of C's type, or
// whose result is one, cannot be called through a box (section 4); a call
// is an error that says why. A box crosses modules in a later step; until
// then an interface shows a box only to C.
//
// Anywhere else a concept in type position is an error that suggests
// `box`. `source` is the program's text, for the requirements' contracts.
// `widened`, when given, is each concept's widened types in this module,
// found by a first pass, for their pack functions and thunks.
void expandErasedBoxes(
    syntax::Node &program, std::string_view source, syntax::Diagnostics &diags,
    const std::map<std::string, std::vector<std::string>> *widened = nullptr,
    int words = 8);

// What a generated function's body is, when it is a box's own op: a
// `pia.box_pack` (pack), a `pia.box_call` (call), a `pia.box_holds`
// (holds) or a `pia.box_unpack` (unpack), else none.
struct BoxOp {
  enum Kind { None, Pack, Call, Holds, Unpack } kind = None;
  std::string descriptor;          // Pack, Holds: the descriptor's symbol
  std::vector<std::string> thunks; // Pack: one per callable requirement
  int entry = 0;                   // Call: which requirement
  int words = 0;                   // Call: the box's words
};
BoxOp boxOp(const syntax::Node &item);

// Why the function `item`, a generated stub, cannot be called through a
// box, or empty when it can.
std::string boxUncallable(const syntax::Node &item);

}  // namespace pia::irgen

#endif  // PIA_IRGEN_BOXES_H
