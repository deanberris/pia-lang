#include "migrate/Migrate.h"

#include <algorithm>

#include "migrate/rules/Rules.h"

namespace pia::migrate {

namespace {

// Orders piac versions as ADR 0073 does: by the commit count on main after
// `+`, which every rule's version has.
unsigned long commits(std::string_view version) {
  size_t plus = version.find('+');
  if (plus == std::string_view::npos)
    return 0;
  unsigned long n = 0;
  for (size_t i = plus + 1;
       i < version.size() && version[i] >= '0' && version[i] <= '9'; ++i)
    n = n * 10 + unsigned(version[i] - '0');
  return n;
}

} // namespace

const std::vector<Rule> &rules() {
  static const std::vector<Rule> all = [] {
    std::vector<Rule> r = {typeMakesDistinct(), boxStates()};
    std::stable_sort(r.begin(), r.end(), [](const Rule &a, const Rule &b) {
      return commits(a.introduced) < commits(b.introduced);
    });
    return r;
  }();
  return all;
}

std::vector<syntax::Lint> find(const syntax::Node &program,
                               std::string_view source, std::string_view from,
                               bool builds, const std::vector<Rule> &all) {
  std::vector<syntax::Lint> out;
  for (const Rule &rule : all) {
    if (builds && !rule.inBuilds)
      continue;
    // A source written for `from` already has every change up to it.
    if (!from.empty() && commits(rule.introduced) <= commits(from))
      continue;
    size_t first = out.size();
    rule.find(rule, program, source, out);
    std::stable_sort(out.begin() + first, out.end(),
                     [](const syntax::Lint &a, const syntax::Lint &b) {
                       return a.loc.offset < b.loc.offset;
                     });
  }
  return out;
}

std::string apply(std::string_view source,
                  const std::vector<syntax::Lint> &lints, size_t &applied) {
  applied = 0;
  // Edits of lints that do not overlap any already taken, then applied
  // back to front so earlier offsets stay valid.
  std::vector<const syntax::TextEdit *> taken;
  auto overlaps = [&](const syntax::TextEdit &e) {
    return std::any_of(taken.begin(), taken.end(), [&](const auto *t) {
      return e.begin < t->end && t->begin < e.end;
    });
  };
  for (const syntax::Lint &l : lints) {
    if (l.edits.empty() || !l.preferred)
      continue;
    if (std::any_of(l.edits.begin(), l.edits.end(), overlaps))
      continue;
    for (const syntax::TextEdit &e : l.edits)
      taken.push_back(&e);
    ++applied;
  }
  std::sort(taken.begin(), taken.end(),
            [](const auto *a, const auto *b) { return a->begin > b->begin; });
  std::string out(source);
  for (const syntax::TextEdit *e : taken)
    out.replace(e->begin, e->end - e->begin, e->text);
  return out;
}

} // namespace pia::migrate
