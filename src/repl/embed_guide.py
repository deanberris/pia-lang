#!/usr/bin/env python3
"""Embeds the agent skills in `pia mcp` as its language guide.

    python3 src/repl/embed_guide.py OUT.inc INSTRUCTIONS.md SKILL.md...

The guide that `:help <topic>` and the `pia://guide/<topic>` resources
serve is cut from the skills' sections, so it cannot drift from them, and
the skills' examples are proved by //tests/docs:skills_test. Every `##`
section of an embedded skill must be listed in TOPICS or SKIPPED: a new
section fails the build until someone decides whether agents need it.
"""

import re
import sys

# (topic, skill directory, section heading or None for the text before the
# first section, one-line summary). The order is the order of :help.
TOPICS = [
    ("start", "pia-language", "Before writing anything",
     "copy a proved example; check a feature exists"),
    ("syntax", "pia-language", "Syntax at a glance",
     "an example and a table of every form"),
    ("facts", "pia-language", "Where each fact goes",
     "types before contracts: the idiom ladder"),
    ("shapes", "pia-language", "The usual shapes",
     "loops, errors, generics, lambdas, modules"),
    ("pitfalls", "pia-language", "Pitfalls",
     "symptom, cause and fix for common mistakes"),
    ("contracts", "pia-contracts", "Start bare, let the goals tell you",
     "the fix for each kind of failed goal"),
    ("loops", "pia-contracts", "Loop invariants",
     "writing loop invariants"),
    ("termination", "pia-contracts", "Termination",
     "decreases on while loops and recursion"),
    ("specs", "pia-contracts", "`old`, quantifiers and spec functions",
     "old, quantifiers, spec functions, lemmas"),
    ("proof-pitfalls", "pia-contracts", "Pitfalls",
     "common contract mistakes"),
    ("results", "pia-mcp", "Reading a result",
     "reading a cell's output"),
    ("workflow", "pia-mcp", "The working loop",
     "the cell-by-cell loop"),
    ("tasks", "pia-mcp", "Long-running work",
     ":spawn, :tasks, :wait and live redefinition"),
    ("session", "pia-mcp", "Pitfalls",
     "common session mistakes"),
    ("example", "pia-mcp", "A replayable example",
     "a whole session with its output"),
]

# Sections an agent connected to the server does not need from the guide.
SKIPPED = {
    ("pia-mcp", "Setup"),               # it is already connected
    ("pia-mcp", "The two tools"),       # the tool descriptions say it
    ("pia-mcp", "Commands you will use"),  # :help lists the commands
    ("pia-mcp", "The built-in guide"),  # it is reading it
}

SITE = "https://pia-lang.dev/"
REPO = "https://github.com/deanberris/pia-lang/blob/main/"
DELIM = "PIA_GUIDE"


def sections(text):
    """{heading or None: body}, with the frontmatter and `#` title dropped."""
    text = re.sub(r"\A---\n.*?\n---\n", "", text, flags=re.S)
    out, name, lines = {}, None, []
    for line in text.splitlines():
        m = re.match(r"## (.*)", line)
        if m:
            out[name] = "\n".join(lines).strip()
            name, lines = m.group(1).strip(), []
        elif not line.startswith("# "):
            lines.append(line)
    out[name] = "\n".join(lines).strip()
    return out


def link(m):
    """Skill links are relative to skills/<name>/; served text has no files."""
    target = m.group(1)
    page = re.match(r"\.\./\.\./docs/([\w/-]+)\.md(#.*)?$", target)
    if page:
        return "](" + SITE + page.group(1) + "/" + (page.group(2) or "") + ")"
    if target.startswith("../../"):
        return "](" + REPO + target[len("../../"):] + ")"
    return m.group(0)


def clean(body):
    body = re.sub(r"<!--.*?-->\n?", "", body, flags=re.S)
    return re.sub(r"\]\(([^)\s]+)\)", link, body).strip() + "\n"


def literal(s):
    if ")" + DELIM + '"' in s:
        sys.exit("embed_guide: the text contains the raw string delimiter")
    return 'R"' + DELIM + "(" + s + ")" + DELIM + '"'


def main():
    out, instructions, skills = sys.argv[1], sys.argv[2], sys.argv[3:]
    parsed = {}
    for path in skills:
        name = path.replace("\\", "/").split("/")[-2]
        with open(path, encoding="utf-8") as f:
            parsed[name] = sections(f.read())
    used = set()
    rows = []
    for topic, skill, heading, summary in TOPICS:
        if heading not in parsed.get(skill, {}):
            sys.exit(f"embed_guide: {skill} has no section '{heading}' "
                     f"for :help {topic}")
        used.add((skill, heading))
        body = parsed[skill][heading]
        # The contracts topic opens with the skill's introduction and table.
        if topic == "contracts":
            body = parsed[skill][None] + "\n\n" + body
        text = "# " + heading + "\n\n" + clean(body)
        rows.append((topic, heading, summary, text))
    for skill, secs in parsed.items():
        for heading in secs:
            if heading is None or (skill, heading) in used | SKIPPED:
                continue
            sys.exit(f"embed_guide: section '{heading}' of {skill} is neither "
                     "a topic nor skipped; add it to TOPICS or SKIPPED in "
                     "src/repl/embed_guide.py")
    with open(instructions, encoding="utf-8") as f:
        primer = clean(f.read())
    with open(out, "w", encoding="utf-8") as f:
        f.write("// Generated by src/repl/embed_guide.py. Do not edit.\n")
        f.write("static const char *const kInstructions =\n    "
                + literal(primer) + ";\n")
        f.write("static const GuideTopic kTopics[] = {\n")
        for topic, heading, summary, text in rows:
            f.write("    {" + ", ".join(literal(x) for x in
                                     (topic, heading, summary, text)) + "},\n")
        f.write("};\n")


if __name__ == "__main__":
    main()
