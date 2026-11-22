#ifndef PIA_IRGEN_REGIONS_H
#define PIA_IRGEN_REGIONS_H

#include <set>
#include <string>

#include "syntax/Diagnostics.h"
#include "syntax/Syntax.h"

namespace pia::irgen {

// Whether `program` has a region parameter, `(r : region)` (ADR 0042,
// step 2), so that eraseRegions has something to do.
bool hasRegions(const syntax::Node &program);

// Region parameters name where borrowed memory comes from without naming
// a value, so that a record can hold both an allocator and the buffers it
// lent: `let vec = let (t : type) (r : region) => type { alloc : bump t r;
// buf : borrowed(r) mutable [t]; len : usize }`. They are erased from
// types, so `vec u16 r` and `vec u16` are one type, and the borrow checker
// keeps them as marks on the syntax that Sema reads:
//
// - each `(r : region)` parameter of a function or a generic type is
//   removed, and so is each region argument of a type application;
// - a function parameter whose type mentions regions is flagged
//   "regions:r,s", and so is the result annotation;
// - a `borrowed(r)` lender that names a region is flagged "region";
// - a record field `borrowed(r) [t]` loses its modifiers, and `vec.buf`
//   is recorded in `lentFields`, since a value holding it may borrow.
struct RegionInfo {
  std::set<std::string> lentFields;  // "type.field"
};
void eraseRegions(syntax::Node &program, syntax::Diagnostics &diags,
                  RegionInfo &info);

}  // namespace pia::irgen

#endif  // PIA_IRGEN_REGIONS_H
