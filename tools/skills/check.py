#!/usr/bin/env python3
"""Checks that the agent skill pack (skills/) is complete and current.

Usage: python3 tools/skills/check.py   (from anywhere in the repository)

The examples and commands inside the skills are run by
//tests/docs:skills_test against the real piac and pia. This script checks
what that test cannot, without building anything, so it runs on every pull
request in seconds (.github/workflows/skills.yml):

1. Every skills/<name>/SKILL.md has front matter whose `name` is <name> and
   whose `description` says when to use it, in at most 1024 characters.
2. Every skill is wired in everywhere it must be: the skills_test list in
   tests/docs/BUILD.bazel, the tables in skills/README.md and
   docs/agents.md, and a .claude/skills/<name> link to ../../skills/<name>.
3. The Claude Code plugin and marketplace manifests (.claude-plugin/) parse
   and agree with each other, and the language server and MCP server they
   start are the repository's own tools.
4. The pack keeps up with the language and the compiler: every keyword the
   lexer knows and every flag piac accepts is mentioned in some skill, in
   code. A feature PR that adds a keyword or a flag fails here until a skill
   teaches it (or the exemption list below says why it need not).

Exit status: 0 when everything holds, 1 otherwise, with one line per
problem.
"""

import json
import os
import re
import subprocess
import sys

# Flags piac accepts that agents have no use for, and why.
FLAG_EXEMPT = {
    # Only for the memory-independence test of solver cost.
    "--memory-ballast",
}

# Keywords that need no teaching of their own, and why.
KEYWORD_EXEMPT = {
    # Spelled out in grammar.md; in code they are the same as their
    # operators.
    "mod",
    # `true` and `false` are values, not features.
    "true",
    "false",
}

# Contextual keywords (src/syntax/Lexer.cpp): keywords only in one place.
CONTEXTUAL = ["spec", "lemma", "reads", "step"]


def root():
    out = subprocess.run(["git", "rev-parse", "--show-toplevel"],
                         capture_output=True, text=True,
                         cwd=os.path.dirname(os.path.abspath(__file__)))
    return out.stdout.strip() if out.returncode == 0 else os.getcwd()


def read(path):
    with open(path, encoding="utf-8") as f:
        return f.read()


def front_matter(text):
    """The `key: value` pairs of a SKILL.md's front matter, or None."""
    if not text.startswith("---\n"):
        return None
    end = text.find("\n---\n", 4)
    if end < 0:
        return None
    fields = {}
    for line in text[4:end].splitlines():
        m = re.match(r"^([A-Za-z_-]+):\s*(.*)$", line)
        if m:
            fields[m.group(1)] = m.group(2).strip()
    return fields


def code_words(text):
    """Every word and flag that appears in code: spans and fenced blocks."""
    fence = r"^[ \t]*```[^\n]*\n(.*?)^[ \t]*```"
    chunks = re.findall(fence, text, re.S | re.M)
    rest = re.sub(fence, "", text, flags=re.S | re.M)
    chunks += re.findall(r"`([^`\n]+)`", rest)
    words = set()
    for c in chunks:
        words.update(re.findall(r"--[a-z][a-z-]*|@?[A-Za-z_][A-Za-z0-9_']*", c))
    return words


def main():
    top = root()
    os.chdir(top)
    problems = []

    skills = sorted(d for d in os.listdir("skills")
                    if os.path.isfile(os.path.join("skills", d, "SKILL.md")))
    texts = {s: read(os.path.join("skills", s, "SKILL.md")) for s in skills}

    # 1. Front matter.
    for s in skills:
        fm = front_matter(texts[s])
        where = f"skills/{s}/SKILL.md"
        if fm is None:
            problems.append(f"{where}: no front matter between --- lines")
            continue
        if fm.get("name") != s:
            problems.append(f"{where}: name is {fm.get('name')!r}, not {s!r}")
        desc = fm.get("description", "")
        if not desc:
            problems.append(f"{where}: no description")
        elif len(desc) > 1024:
            problems.append(f"{where}: description is {len(desc)} characters, over 1024")
        elif "Use when" not in desc:
            problems.append(f"{where}: description should say 'Use when ...'")
        if "<" in desc or ">" in desc:
            problems.append(f"{where}: description has angle brackets")

    # 2. Wiring.
    build = read("tests/docs/BUILD.bazel")
    readme = read("skills/README.md")
    agents = read("docs/agents.md")
    for s in skills:
        if f'"//skills:{s}/SKILL.md"' not in build:
            problems.append(f"tests/docs/BUILD.bazel: {s} is not in SKILLS, so skills_test does not run its examples")
        if f"[{s}](" not in readme:
            problems.append(f"skills/README.md: {s} is not in the table")
        if f"[`{s}`](" not in agents:
            problems.append(f"docs/agents.md: {s} is not in the table")
        link = os.path.join(".claude", "skills", s)
        if os.readlink(link) != f"../../skills/{s}" if os.path.islink(link) else True:
            problems.append(f"{link}: should be a link to ../../skills/{s}")
    for d in os.listdir(os.path.join(".claude", "skills")):
        if d not in skills:
            problems.append(f".claude/skills/{d}: links to no skill")

    # 3. Manifests.
    try:
        plugin = json.loads(read(".claude-plugin/plugin.json"))
        market = json.loads(read(".claude-plugin/marketplace.json"))
    except (OSError, ValueError) as e:
        problems.append(f".claude-plugin: {e}")
    else:
        entries = [p for p in market.get("plugins", [])
                   if p.get("name") == plugin.get("name")]
        if len(entries) != 1:
            problems.append(".claude-plugin/marketplace.json: no single entry for the plugin in plugin.json")
        elif entries[0].get("source") != "./":
            problems.append(".claude-plugin/marketplace.json: the plugin's source should be ./, the repository root, so skills/ and the docs they link to are installed")
        for key in ("name", "owner", "plugins"):
            if key not in market:
                problems.append(f".claude-plugin/marketplace.json: no {key}")
        mcp = plugin.get("mcpServers", {}).get("pia", {})
        if mcp.get("command") != "pia" or mcp.get("args") != ["mcp"]:
            problems.append(".claude-plugin/plugin.json: mcpServers.pia should run `pia mcp`")
        lsp = plugin.get("lspServers", {}).get("pia", {})
        if lsp.get("command") != "pia-lsp":
            problems.append(".claude-plugin/plugin.json: lspServers.pia should run pia-lsp")
        exts = lsp.get("extensionToLanguage", {})
        if exts.get(".pia") != "pia":
            problems.append(".claude-plugin/plugin.json: lspServers.pia should map .pia files to the language pia")

    # 4. Coverage of keywords and flags.
    taught = set()
    for t in texts.values():
        taught |= code_words(t)
    lexer = read("src/syntax/Lexer.cpp")
    table = lexer[lexer.find("keywords()"):]
    table = table[:table.find("};")]
    keywords = re.findall(r'\{"([a-z]+)"', table) + CONTEXTUAL
    for k in keywords:
        if k not in taught and k not in KEYWORD_EXEMPT:
            problems.append(f"skills: the keyword `{k}` (src/syntax/Lexer.cpp) is in no skill's code; teach it, or exempt it in tools/skills/check.py with a reason")
    flags = sorted(set(re.findall(r'"(--[a-z][a-z-]*)', read("tools/piac/piac.cpp"))))
    for f in flags:
        if f not in taught and f not in FLAG_EXEMPT:
            problems.append(f"skills: the piac flag `{f}` (tools/piac/piac.cpp) is in no skill's code; teach it, or exempt it in tools/skills/check.py with a reason")

    for p in problems:
        print(p)
    if problems:
        print(f"{len(problems)} problem(s); see tools/skills/check.py")
        return 1
    print(f"skills: {len(skills)} skills, {len(keywords)} keywords and {len(flags)} piac flags covered")
    return 0


if __name__ == "__main__":
    sys.exit(main())
