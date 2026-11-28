// Migration rules (ADR 0073, section 5): every change after which source
// that piac accepted is rejected or means something else ships a rule that
// finds the old form and either rewrites it or says what to write instead.
//
// A rule reads the parsed syntax tree, before metaprograms run, and reports
// each old form as a lint (syntax/Lint.h) named after the rule: a message,
// and the edits of its rewrite when one is safe. So the language server
// offers a rewrite as a quick fix with no code of its own, and `piac
// migrate` applies the rewrites and lists the rest. The library has no LLVM
// dependency, like src/syntax.
//
// A rule for a deprecated form runs in every build too, as a `deprecated`
// warning, for the release in which the old form still compiles. A rule
// for a change of meaning, where the old source still compiles but means
// something else, runs only in `piac migrate`, since in a build it would
// flag every use of the new meaning.

#ifndef PIA_MIGRATE_MIGRATE_H
#define PIA_MIGRATE_MIGRATE_H

#include <string>
#include <string_view>
#include <vector>

#include "syntax/Lint.h"
#include "syntax/Syntax.h"

namespace pia::migrate {

struct Rule {
  std::string id;         // `type-makes-distinct`
  std::string introduced; // the piac version of the change, `0.0.0+634`
  std::string summary;    // one line: what changed
  std::string adr;        // where the change is explained
  // Whether every build reports it, as a `deprecated` warning.
  bool inBuilds = false;
  // Appends a lint named `id` for each old form in `program`.
  void (*find)(const Rule &rule, const syntax::Node &program,
               std::string_view source, std::vector<syntax::Lint> &out);
};

// Every rule, oldest first.
const std::vector<Rule> &rules();

// What the rules introduced after `from` find in `program`, in rule order
// and then source order. An empty `from` runs every rule. With `builds`,
// only the rules that report in every build run.
std::vector<syntax::Lint> find(const syntax::Node &program,
                               std::string_view source, std::string_view from,
                               bool builds,
                               const std::vector<Rule> &all = rules());

// `source` with the preferred edits of `lints` applied. An edit that
// overlaps one already applied is left for the next pass, and `applied`
// counts the lints whose edits went in.
std::string apply(std::string_view source,
                  const std::vector<syntax::Lint> &lints, size_t &applied);

} // namespace pia::migrate

#endif // PIA_MIGRATE_MIGRATE_H
