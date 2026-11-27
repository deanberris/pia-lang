// Interface artifacts and imports across files (ADR 0039, step 2).
//
// `piac --emit=interface` writes one `.piai` file per interface a module
// declares. An artifact is Pia source in a canonical form: the module's
// header and the interface, with comments dropped and whitespace
// normalised, so a change that does not change the interface (a comment, a
// private item, a body) leaves it byte-identical. Its SHA-256 is the
// interface hash.
//
// An importer finds `import M.I` as `M.I.piai` on its interface path. Each
// function the interface lists becomes a bodyless item named `M.f`, which
// callers reach as `M.f` and are checked against: its body is in M.

#ifndef PIA_SYNTAX_INTERFACES_H
#define PIA_SYNTAX_INTERFACES_H

#include <string>
#include <string_view>
#include <vector>

#include "syntax/Diagnostics.h"
#include "syntax/Embeds.h"
#include "syntax/Syntax.h"

namespace pia::syntax {

struct InterfaceArtifact {
  std::string module;  // `Image.Png`
  std::string name;    // `Codec`
  std::string text;    // the canonical source

  // `Image.Png.Codec.piai`
  std::string fileName() const { return module + "." + name + ".piai"; }
};

// The artifacts of the interfaces `program` declares, from the tokens of
// `source`, which `program` was parsed from. A program with interfaces
// needs a module header, which names them. `embeds` is consulted only when an
// interface explicitly exports an `@embed` binding (ADR 0070, section 5).
std::vector<InterfaceArtifact>
interfaceArtifacts(const Node &program, std::string_view source, bool literate,
                   Diagnostics &diags, const EmbedOptions *embeds = nullptr);

// Replaces each `import M.I` with the items of `M.I.piai`, found in the
// first directory of `paths` that has it, and rewrites `M.f` in the
// program to name them. An `import T` of a theory the program declares is
// left for the theories (ADR 0036).
// `loaded`, if given, gets each artifact imported, for its witness symbol
// (docs/abi.md).
void resolveImports(Node &program, const std::vector<std::string> &paths,
                    Diagnostics &diags,
                    std::vector<InterfaceArtifact> *loaded = nullptr);

// Gives each function that an interface of this file lists, and whose
// definition states no contract, that interface's contract, with its
// parameters renamed to the definition's (ADR 0077). The definition is then
// proved against it, and callers in the module use it, as if it had been
// written there. A `decreases` measure alone is not a contract.
void inheritInterfaceContracts(Node &program, Diagnostics &diags);

}  // namespace pia::syntax

#endif  // PIA_SYNTAX_INTERFACES_H
