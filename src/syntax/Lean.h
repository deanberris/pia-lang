// The Lean 4 translation of a program's specification (ADR 0061).
//
// `piac --emit-lean` writes the statement of each lemma proved in Lean,
// `let lemma l ... = by lean T`, as a Lean `Prop`, together with every spec
// function and record type the statement uses. A Lean proof then proves
// `T : l` against that file, and its receipt names the statement by the
// SHA-256 of the statement's text and the definitions it uses. Only the
// specification is translated, never code, so Lean gives no second meaning
// to what the program does.

#ifndef PIA_SYNTAX_LEAN_H
#define PIA_SYNTAX_LEAN_H

#include <string>
#include <vector>

#include "syntax/Diagnostics.h"
#include "syntax/Syntax.h"

namespace pia::syntax {

// One lemma proved in Lean.
struct LeanStatement {
  std::string lemma;   // the Pia lemma, which is also the Lean `Prop`
  std::string theorem; // the Lean theorem that `by lean` names
  // The Lean text of the statement and of every definition it uses, in
  // the order the file has them. Its SHA-256 is the statement hash, so a
  // change to the lemma or to anything it means makes old receipts stale.
  std::string closure;
  SourceLoc loc;
};

struct LeanFile {
  // The definitions and statements, inside `namespace <ns>`.
  std::string text;
  std::vector<LeanStatement> statements;
};

// Translates the `by lean` lemmas of an expanded program, and what they
// use, into Lean in namespace `ns`. A construct with no translation yet is
// an error at its location; a program with no `by lean` lemma gives an
// empty file.
LeanFile emitLean(const Node &program, const std::string &ns,
                  Diagnostics &diags);

// The lemmas of a program proved in Lean, as (lemma, theorem) pairs.
std::vector<std::pair<std::string, std::string>>
leanLemmas(const Node &program);

} // namespace pia::syntax

#endif // PIA_SYNTAX_LEAN_H
