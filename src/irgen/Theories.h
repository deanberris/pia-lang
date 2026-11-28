#ifndef PIA_IRGEN_THEORIES_H
#define PIA_IRGEN_THEORIES_H

#include <map>
#include <set>
#include <string>
#include <utility>
#include <vector>

#include "syntax/Diagnostics.h"
#include "syntax/Syntax.h"

namespace pia::irgen {

// Whether `program` declares a theory or marks the file (ADR 0036), so
// that flattenTheories has something to do.
bool hasTheories(const syntax::Node &program);

// Whether the file is marked `@trusted`, on a line of its own or in its
// module header, `module M @trusted : I` (ADR 0023, ADR 0039). Only such a
// file may declare a theory without a model or use `assume`.
bool isTrustedFile(const syntax::Node &program);

// Replaces each `let theory T = sig ... end` with its items, named `T.x`:
// a sort becomes a type item, an abstract spec function a bodyless spec
// item ("spec abstract"), and axioms, spec functions and lemmas keep their
// flags. Inside the theory, members are used unqualified; everywhere,
// `T.x` names them. Also checks the theory rules of step 2: no shadowing
// (ADR 0022), axioms only in a file marked `@trusted`, and `import T` of a
// theory in the same program, which is a no-op.
//
// A model `let model m : T = struct ... end` (step 3) becomes items named
// `m.x`, and each axiom of T a lemma `m.a`, the axiom with the model's
// sorts and functions in place of T's: the model check. A theory with a
// model needs no @trusted. Clients still see only T's abstract functions
// and axioms, so the model is sealed.
struct TheoryInfo {
  // `m.a` -> {model m, axiom T.a}: the lemmas of the model check.
  std::map<std::string, std::pair<std::string, std::string>> obligations;
  std::map<std::string, std::string> modelOf;   // a model's item -> model
  std::map<std::string, std::string> modelled;  // theory -> its model
  // `m.witness.f` -> `f`: a client with the model's definitions in place
  // of the theory's, where a failed goal looks for a counterexample.
  std::map<std::string, std::string> witnesses;
  // `import T trusting`: each theory a module trusts, and where.
  std::vector<std::pair<std::string, syntax::SourceLoc>> trusting;
  // `@target(m)` functions -> m (ADR 0049): their proofs see the model's
  // values of `Target`'s functions, not only its axioms.
  std::map<std::string, std::string> targetOf;
  // A box's theory over the box itself (ADR 0046), whose consistency
  // follows from its one-byte shape's: its axioms speak of one box at a
  // time and never of its words. The shape's is checked instead, since the
  // check grows with every word of the box (#563).
  std::set<std::string> boxModelled;
};
void flattenTheories(syntax::Node &program, syntax::Diagnostics &diags,
                     TheoryInfo *info = nullptr);

}  // namespace pia::irgen

#endif  // PIA_IRGEN_THEORIES_H
