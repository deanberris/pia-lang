#include "repl/Guide.h"

#include <algorithm>
#include <iterator>
#include <set>

namespace pia::repl {

namespace {

#include "repl/GuideText.inc"

// A diagnostic, recognised by a fragment of its text, and what to do about
// it. The fragments are the verifier's and parser's own wording; the hints
// say the fix in a line and name the topic with the rest, so an agent can
// recover without reading the whole guide. tests/repl/mcp_test.py checks
// that real failures get them.
struct Hint {
  const char *fragment;
  const char *topic;
  const char *text;
};

constexpr Hint kHints[] = {
    {"' shadows ", "pitfalls",
     "Pia has no shadowing: pick a new name (primes work, as in x'), or "
     "replace a committed definition with :redef."},
    {"does not overflow", "facts",
     "arithmetic is checked at the operands' width: bound the inputs with a "
     "range type (int{0..99}) or a requires, or widen with a typed let."},
    {"the value fits in ", "facts",
     "narrowing is a goal: bound the value with a range type or a requires, "
     "or keep the wider type."},
    {"is within bounds", "contracts",
     "guard the access with an if, or make the length the caller's business "
     "with requires len xs > i."},
    {"the precondition of '", "contracts",
     "the caller proves the callee's requires: add a guard, a requires "
     "here, or an ensures on whatever produced the argument."},
    {"the postcondition holds", "contracts",
     "either the ensures is wrong, or the body lost a fact: callers see only "
     "a callee's ensures, and after a loop only its invariant."},
    {"the loop invariant holds", "loops",
     "an invariant must hold on entry and survive one iteration on its own; "
     "bound accumulators by the loop variable."},
    {"the measure decreases", "termination",
     "decreases m must be non-negative and go down on every iteration or "
     "recursive call."},
    {"terminates", "termination",
     "a while loop or a recursive function needs decreases m."},
    {"not supported yet", "start",
     "this is designed but not built; https://pia-lang.dev/status/ lists "
     "what compiles."},
    {"expected an expression", "syntax",
     "`//` is not a comment, `|` is bitwise or only inside brackets, and an "
     "inner let after then, or a body right after ensures, needs "
     "parentheses."},
    {"expected the end of the item", "syntax",
     "a top-level item ended early: check for `//`, a missing `in`, or a "
     "bare `|` outside brackets."},
    {"unexpected character", "syntax",
     "comments are (* *) and \\ to the end of the line; `//` is not one."},
};

constexpr size_t kMaxHints = 3;

} // namespace

const std::vector<GuideTopic> &guideTopics() {
  static const std::vector<GuideTopic> topics(std::begin(kTopics),
                                              std::end(kTopics));
  return topics;
}

const GuideTopic *findGuideTopic(std::string_view name) {
  for (const GuideTopic &t : guideTopics())
    if (name == t.name)
      return &t;
  return nullptr;
}

std::string guideTopicList() {
  size_t width = 0;
  for (const GuideTopic &t : guideTopics())
    width = std::max(width, std::string_view(t.name).size());
  std::string out;
  for (const GuideTopic &t : guideTopics()) {
    std::string name = t.name;
    out += "  " + name + std::string(width + 2 - name.size(), ' ') + t.summary +
           "\n";
  }
  return out;
}

std::string guideInstructions() {
  return std::string(kInstructions) + guideTopicList();
}

std::string guideHints(std::string_view failure) {
  std::string out;
  std::set<std::string_view> topics;
  for (const Hint &h : kHints) {
    if (topics.size() == kMaxHints)
      break;
    if (failure.find(h.fragment) == std::string_view::npos)
      continue;
    // One hint per topic: two overflows in a cell need one reminder.
    if (!topics.insert(h.topic).second)
      continue;
    out += std::string("hint: ") + h.text + " (:help " + h.topic + ")\n";
  }
  return out;
}

} // namespace pia::repl
