// The built-in theory `Memory`, RC11 (ADR 0052, section 4), written in
// src/irgen/Memory.pia and compiled into piac. tests/memory/theory.pia
// proves its model.

#ifndef PIA_IRGEN_MEMORY_H
#define PIA_IRGEN_MEMORY_H

#include <string_view>

#include "syntax/Diagnostics.h"
#include "syntax/Syntax.h"

namespace pia::irgen {

// The source of the theory `Memory` and its model `timeline`.
std::string_view memoryTheorySource();

// Whether `program` names `Memory`, as `Memory.x` or a type `Memory.t`,
// and does not define an item `Memory` itself.
bool usesMemoryTheory(const syntax::Node &program);

// Puts the theory `Memory` and its model in front of `program`'s items,
// both marked "builtin", so flattenTheories does not prove the model again.
// Returns false, with an error, if the built-in source does not expand.
bool addMemoryTheory(syntax::Node &program, syntax::Diagnostics &diags);

} // namespace pia::irgen

#endif // PIA_IRGEN_MEMORY_H
