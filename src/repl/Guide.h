// The language guide that `pia mcp` teaches an agent with: the server's
// instructions, the topics of `:help <topic>` and the `pia://guide/<topic>`
// resources, and hints attached to failed cells (ADR 0031, "Teaching the
// language").
//
// The text is cut from the agent skills (skills/pia-language,
// skills/pia-contracts, skills/pia-mcp) at build time by
// src/repl/embed_guide.py, so the server and the skills cannot drift, and
// the skills' examples are proved by //tests/docs:skills_test.

#ifndef PIA_REPL_GUIDE_H
#define PIA_REPL_GUIDE_H

#include <string>
#include <string_view>
#include <vector>

namespace pia::repl {

struct GuideTopic {
  const char *name;    // what :help takes, such as "syntax"
  const char *title;   // the skill section it comes from
  const char *summary; // one line, for the topic list
  const char *text;    // Markdown
};

// Every topic, in the order :help lists them.
const std::vector<GuideTopic> &guideTopics();

// The topic called `name`, or null.
const GuideTopic *findGuideTopic(std::string_view name);

// The topic list, one "  name  summary" line each.
std::string guideTopicList();

// The MCP server's `instructions`: a short primer and the topic list.
std::string guideInstructions();

// Hint lines ("hint: ... (:help topic)") for the diagnostics in a failed
// cell's text, at most a few, each topic once.
std::string guideHints(std::string_view failure);

} // namespace pia::repl

#endif // PIA_REPL_GUIDE_H
