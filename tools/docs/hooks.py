"""MkDocs hooks for the Pia documentation site (mkdocs.yml).

Pages link to source files outside docs/ with relative paths such as
`../src/syntax/Prelude.cpp`, which work on GitHub. The site has no copy of
those files, so this rewrites each such link to the file on GitHub.
"""

import posixpath
import re

REPO = "https://github.com/deanberris/pia-lang"
LINK = re.compile(r"\]\((\.\./[^)\s#]*)(#[^)\s]*)?\)")


def on_page_markdown(markdown, page, config, files):
    page_dir = posixpath.dirname(page.file.src_uri)

    def rewrite(m):
        target = posixpath.normpath(posixpath.join("docs", page_dir, m.group(1)))
        if target == "docs" or target.startswith("docs/"):
            return m.group(0)
        kind = "tree" if target.endswith("/") or "." not in posixpath.basename(target) else "blob"
        return f"]({REPO}/{kind}/main/{target}{m.group(2) or ''})"

    return LINK.sub(rewrite, markdown)
