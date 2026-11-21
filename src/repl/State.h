// State in the REPL (ADR 0031, "State"): a top-level
//
//   let count : mutable u32 = 0
//     invariant count <= 100
//
// is a value that persists between cells. The session keeps its storage,
// and the verifier sees it as what it is: every definition that uses the
// state, directly or through a call, takes it as a `borrowed inout mutable`
// one-element buffer, so the existing proofs about buffers, calls and `old`
// apply unchanged. Each such definition also requires the invariant and
// ensures it, and one that never writes the state ensures it is unchanged.
//
// The rewrite relies on the no-shadowing rule (ADR 0022): a name that is a
// state's name means the state wherever it appears.

#ifndef PIA_REPL_STATE_H
#define PIA_REPL_STATE_H

#include <functional>
#include <map>
#include <set>
#include <string>
#include <vector>

#include "syntax/Syntax.h"

namespace pia::repl {

// The hidden function whose body is a state's initial value, and which
// proves that value meets the invariant.
inline constexpr const char *kInitPrefix = "__pia_init_";

struct StateDecl {
  std::string name;
  syntax::NodePtr type;       // the element type, without `mutable`
  syntax::NodePtr invariant;  // null for none
  syntax::SourceLoc loc;
  // Its initial value names `old <name>`: the value of the definition it
  // replaces, which its `__pia_init_` function then takes as a buffer, under
  // the old invariant, and migrates to the new type and invariant.
  bool migrates = false;
};

struct StateUse {
  std::vector<StateDecl> states;  // in the order they are defined
  // The states each rewritten definition takes, in that order.
  std::map<std::string, std::vector<std::string>> uses;
  std::set<std::string> writes;  // definitions that may change a state
  // Definitions written with `()` that now take only states.
  std::set<std::string> unitFns;
};

// Whether `item` is a state: a `let` with no parameters whose annotation
// says `mutable`.
bool isStateItem(const syntax::Node &item);

// Replaces each state item in `program` by its `__pia_init_` function, and
// rewrites every definition that uses a state. `extra` are definitions kept
// outside the program (the old versions of replaced ones), rewritten the
// same way. Errors (an invariant on a definition that is not a state, a
// state's initial value that uses state) go to `errors` as (loc, message).
// Only a state for which `isNew` holds gets an `__pia_init_` function: the
// others keep the value they have.
StateUse rewriteState(
    syntax::Node &program, const std::vector<syntax::Node *> &extra,
    const std::function<bool(const syntax::Node &)> &isNew,
    std::vector<std::pair<syntax::SourceLoc, std::string>> &errors);

}  // namespace pia::repl

#endif  // PIA_REPL_STATE_H
