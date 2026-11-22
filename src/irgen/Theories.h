#ifndef PIA_IRGEN_THEORIES_H
#define PIA_IRGEN_THEORIES_H

#include "syntax/Diagnostics.h"
#include "syntax/Syntax.h"

namespace pia::irgen {

// Whether `program` declares a theory or marks the file (ADR 0036), so
// that flattenTheories has something to do.
bool hasTheories(const syntax::Node &program);

// Replaces each `let theory T = sig ... end` with its items, named `T.x`:
// a sort becomes a type item, an abstract spec function a bodyless spec
// item ("spec abstract"), and axioms, spec functions and lemmas keep their
// flags. Inside the theory, members are used unqualified; everywhere,
// `T.x` names them. Also checks the theory rules of step 2: no shadowing
// (ADR 0022), axioms only in a file marked `@trusted`, and `import T` of a
// theory in the same program, which is a no-op.
void flattenTheories(syntax::Node &program, syntax::Diagnostics &diags);

}  // namespace pia::irgen

#endif  // PIA_IRGEN_THEORIES_H
