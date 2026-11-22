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
// concept C there, and `box C` is then its own type, `box_C`: the tagged
// union of the types this module widens to C (step 5, the module's closed
// world). What the object is, the verifier knows only through C: each
// requirement `r` with one receiver of C's type is an uninterpreted
// function `erased_C.r_of` of the box, its contract an axiom
// of it, and each law of C over one value an axiom too, in the theory
// `erased_C`. Those axioms hold because `widen` runs the use check: every
// type it boxes meets C, contracts and laws included. So
//
// - `widen b`, for a full `box t` with t meeting C, makes a `box_C`;
// - `r b` calls the requirement through the box, a switch on the tag in
//   code: its precondition is a goal at the call, and its result is, to
//   the verifier, `erased_C.r_of b`, about which the contract and laws say
//   what they say;
// - those functions are `box_C`'s instance of C, so `box C` meets C and
//   generic code instantiates at it.
//
// A requirement whose receiver is not the only value of C's type, or
// whose result is one, cannot be called through a box (section 4); a call
// is an error that says why. Tables of function pointers, so that a box
// can cross modules, are step 6; until then an interface shows a box only
// to C.
//
// Anywhere else a concept in type position is an error that suggests
// `box`. `source` is the program's text, for the requirements' contracts.
// `widened`, when given, is each concept's widened types in this module,
// found by a first pass: `box C` is then their tagged union, and a call
// through it a switch (ADR 0046, step 5).
void expandErasedBoxes(
    syntax::Node &program, std::string_view source, syntax::Diagnostics &diags,
    const std::map<std::string, std::vector<std::string>> *widened = nullptr);

// Why the function `item`, a generated stub, cannot be called through a
// box, or empty when it can.
std::string boxUncallable(const syntax::Node &item);

}  // namespace pia::irgen

#endif  // PIA_IRGEN_BOXES_H
