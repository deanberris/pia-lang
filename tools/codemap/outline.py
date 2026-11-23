#!/usr/bin/env python3
"""Prints the outline of a source file: its definitions with line numbers.

    python3 tools/codemap/outline.py src/irgen/IRGen.cpp
    python3 tools/codemap/outline.py --min-lines 1 --grep coerce src/irgen/IRGen.cpp

An agent (or a person) reads the outline instead of the file, then opens only
the lines it needs, e.g. `sed -n 753,1175p src/irgen/IRGen.cpp`. CODEMAP.md
says which files are big enough to want it.

C++ (.cpp, .h): functions and methods with their line ranges, and the first
line of the comment above each. TableGen (.td): defs. Pia (.pia, .pia.md):
module, interface, imports and top-level lets. Python: defs and classes.
Markdown: headings. The C++ reader is a heuristic for this repository's
LLVM style (a definition ends at the closing brace at its own indentation);
it is a map, not a parser.
"""

import argparse
import re
import signal
import sys

CPP_DEF = re.compile(
    r"^(?P<ind> *)(?:template <.*> )?(?:static |inline |virtual |explicit |constexpr )*"
    r"(?P<sig>[A-Za-z_][\w:<>,\*& ]*?[\s\*&](?P<name>~?[A-Za-z_][\w:]*(?:<[^>]*>)?)\(.*)$"
)
CPP_TYPE = re.compile(r"^(?P<ind> *)(?:class|struct|namespace) (?P<name>[\w:]+)?.*\{\s*$")
NOT_DEF = re.compile(r"^\s*(return|if|for|while|else|case|switch|do|delete|new|throw|using|typedef)\b")


def comment_above(lines, i):
    """The first line of the // comment block ending just above line i."""
    j = i - 1
    while j >= 0 and lines[j].strip().startswith("//"):
        j -= 1
    if j + 1 < i:
        return lines[j + 1].strip().lstrip("/").strip()
    return ""


def cpp(lines, min_lines):
    out = []
    i = 0
    while i < len(lines):
        line = lines[i]
        m = CPP_TYPE.match(line)
        if m and len(m.group("ind")) <= 2:
            kind = line.split()[0]
            out.append((i + 1, None, f"{m.group('ind')}{kind} {m.group('name') or '(anonymous)'}", ""))
            i += 1
            continue
        m = CPP_DEF.match(line)
        if not m or NOT_DEF.match(line) or len(m.group("ind")) > 2:
            i += 1
            continue
        # The signature may span lines; it is a definition if it reaches `{`
        # before `;`.
        j = i
        while j < len(lines) and "{" not in lines[j] and not lines[j].rstrip().endswith(";"):
            j += 1
        if j >= len(lines) or "{" not in lines[j]:
            i += 1
            continue
        ind = m.group("ind")
        end = j
        if lines[j].count("{") > lines[j].count("}"):
            end = j + 1
            while end < len(lines) and lines[end].rstrip() not in (ind + "}", ind + "};"):
                end += 1
        n = end - i + 1
        if n >= min_lines:
            out.append((i + 1, end + 1, ind + m.group("name"), comment_above(lines, i)))
        i = end + 1
    return out


def simple(lines, pattern):
    rx = re.compile(pattern)
    return [(i + 1, None, l.rstrip()[:110], "") for i, l in enumerate(lines) if rx.match(l)]


def outline(path, lines, min_lines):
    if path.endswith((".cpp", ".h", ".cc")):
        return cpp(lines, min_lines)
    if path.endswith(".td"):
        return simple(lines, r"^(def|class|multiclass) ")
    if path.endswith((".pia", ".pia.md")):
        return simple(lines, r"^(module|interface|import|let|  let) |^```pia")
    if path.endswith(".py") or path.endswith(".bzl"):
        return simple(lines, r"^\s*(def|class) ")
    if path.endswith(".md"):
        return simple(lines, r"^#+ ")
    sys.exit(f"outline: no reader for {path}")


def main():
    signal.signal(signal.SIGPIPE, signal.SIG_DFL)
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="+")
    ap.add_argument("--min-lines", type=int, default=8,
                    help="C++ only: leave out functions shorter than this (default 8)")
    ap.add_argument("--grep", help="only entries whose name or comment matches this regex")
    args = ap.parse_args()
    for path in args.files:
        with open(path, encoding="utf-8") as f:
            lines = f.read().split("\n")
        print(f"== {path} ({len(lines)} lines)")
        for start, end, name, note in outline(path, lines, args.min_lines):
            if args.grep and not re.search(args.grep, name + " " + note):
                continue
            span = f"{start}-{end}" if end else f"{start}"
            print(f"{span:>11}  {name}" + (f"  // {note[:80]}" if note else ""))


if __name__ == "__main__":
    main()
