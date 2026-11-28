// ADR 0064 (#425): before it, `let blk = type int{0..63}` named int{0..63};
// since, `type e` makes a new type, distinct from `e`, and an alias is
// spelled `let blk = int{0..63}`. The old source still compiles, so the
// rule runs only in `piac migrate`. Which one the author meant is a
// question of intent, so it is a suggestion: its edit, which keeps the old
// meaning, is offered but never applied blindly.

#include "migrate/rules/Rules.h"

namespace pia::migrate {

namespace {

void find(const Rule &rule, const syntax::Node &program,
          std::string_view source, std::vector<syntax::Lint> &out) {
  using syntax::NodeKind;
  for (const syntax::NodePtr &item : program.kids) {
    if (item->kind != NodeKind::LetItem || item->kids.size() < 4 ||
        item->kids[3]->kind != NodeKind::TypeValue)
      continue;
    const syntax::Node &value = *item->kids[3];
    if (value.kids.empty())
      continue;
    const syntax::Node &body = *value.kids[0];
    // A record, a variant or a refinement was always a new type.
    if (body.kind == NodeKind::RecordType || body.kind == NodeKind::Variants ||
        body.kind == NodeKind::RefinementType)
      continue;
    if (body.loc.offset <= value.loc.offset || body.loc.offset > source.size())
      continue;
    syntax::Lint l;
    l.name = rule.id;
    l.loc = value.loc;
    l.end = body.loc.offset;
    l.message = "'" + item->text +
                "' is a new type, distinct from what follows 'type', since " +
                rule.adr +
                "; before, it was another name for it. If you meant "
                "another name, drop 'type'";
    l.fixTitle = "Keep '" + item->text + "' another name: drop 'type'";
    l.edits.push_back({value.loc.offset, body.loc.offset, ""});
    l.preferred = false;
    out.push_back(std::move(l));
  }
}

} // namespace

Rule typeMakesDistinct() {
  return {"type-makes-distinct",
          "0.0.0+634",
          "`let n = type e` makes a new type, no longer another name for e",
          "ADR 0064",
          /*inBuilds=*/false,
          find};
}

} // namespace pia::migrate
