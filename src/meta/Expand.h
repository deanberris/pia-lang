// Metaprogram expansion (milestone M7, ADR 0007 and ADR 0008).
//
// Runs a program's metaprograms to a fixed point: `@derive(...)` on types,
// top-level calls of `let meta` functions, and the operator declarations of
// the prelude and the program, which turn each binary operator into a call
// of a core builtin. Then removes the metaprograms, so Sema sees ordinary
// code. docs/meta.md describes the language and the loop.

#ifndef PIA_META_EXPAND_H
#define PIA_META_EXPAND_H

#include "syntax/Diagnostics.h"
#include "syntax/Syntax.h"

namespace pia::meta {

struct Options {
  // The most passes that may still produce code (`--meta-cycles=N`).
  unsigned maxCycles = 32;
  // Whether the REPL-only builtins of Pia.Live are available, such as
  // `redefine` (ADR 0031). Only `pia repl` sets it; compiled programs
  // never have them.
  bool live = false;
};

// Expands `program` in place. Reports each failure to `diags` and returns
// false if there was one.
bool expand(syntax::Node &program, syntax::Diagnostics &diags,
            const Options &options = {});

}  // namespace pia::meta

#endif  // PIA_META_EXPAND_H
