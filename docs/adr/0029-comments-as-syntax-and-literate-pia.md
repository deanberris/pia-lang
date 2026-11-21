# 29. Comments are syntax: `\` line comments, doc comments, and literate `.pia.md` files

Date: 2026-11-21

Status: Accepted

## Context

Pia has one kind of comment, OCaml's nesting `(* ... *)` ([grammar.md](../grammar.md#whitespace-and-comments)), and the lexer throws it away. Two things are missing.

**A line comment.** Short notes at the end of a line are awkward as block comments. The obvious spellings are taken or reserved: `//` and `--` are kept as future operators, `#` is kept for directives, `;;` is the item separator and `;` is sequencing. Every run of operator characters (`+ - * / < > = | & ^ ~ ! % ?`) is a possible operator, so any spelling built from them, such as `%%`, would take a symbol away from the operator space for good.

**Comments a program can see.** Dean wants literate programming: a metaprogram should be able to walk a listing and see the prose as well as the code. Uses include checking that every exported function is documented, copying documentation into generated code, the language server showing a definition's documentation on hover, and later a library that renders listings as LaTeX, HTML, SVG or DOT ([#63](https://github.com/deanberris/pia-lang/issues/63)) and a Jupyter kernel ([#64](https://github.com/deanberris/pia-lang/issues/64)). None of this works if the lexer discards comments.

Compilers that keep comments do it in one of two ways. Roslyn and Swift keep *trivia* on every token, which round-trips source exactly but makes every consumer step over it. Go's `ast.CommentMap` and rustc's doc attributes attach comments to the nearest syntax node, which is what a reader means by "the comment on this function". Pia's metaprograms work on nodes, so the second fits.

## Decision

### Lexical

1. **`\` starts a line comment** that runs to the end of the line. Backslash is not used anywhere else outside string literals, so this takes nothing away from operators, directives or separators. It is Forth's line comment.

   ```ocaml
   let tile : u32 = 16  \ elements per SIMD tile
   ```

2. **`(* ... *)` is unchanged.** It still nests, and `(*` still always opens a comment, so multiplication as a value is still `( * )`.
3. **`(** ... *)` is a doc comment**, as in OCaml. `(**)` is an empty ordinary comment, and `(***` starts an ordinary comment, so banner lines of stars stay ordinary.
4. Comments are still invisible to the layout rule and to the phrase grammar. A comment can go anywhere whitespace can, and no program changes meaning.

### Comments in the syntax tree

5. **Every comment is kept as a `Comment` node** with a *style* (`line`, `block`, `doc` or `prose`), a *place* (`leading`, `trailing` or `detached`) and its text. The text is the comment's content without its delimiters, trimmed of surrounding whitespace. Line comments on consecutive lines, each alone on its line, merge into one comment, so a paragraph written with `\` is one node.
6. **Comments are attached to the node they describe**, not stored as items. A node keeps its comments beside its children, so no existing pass, child index or golden test changes. The parser attaches each comment once:
   - A **trailing** comment has code before it on its line, and nothing after it. It goes to the outermost node that ends at the token before it and starts on that line, or, if no node starts on that line (as with `done`), to the innermost node that ends there. A `;`, `,` or `in` before it is skipped. After a token that leads into what follows, such as `=`, `then` or an opening bracket, the comment leads instead.
   - Any other comment goes to the outermost node that starts at the next token. It is **leading** if no blank line separates them, and **detached** otherwise, like a section heading or a licence header.
   - A comment with no token after it goes to the program, as detached.
7. **Hygiene does not apply to comments.** Comments bind no names and refer to none, so renaming never looks inside them and a name in a comment never resolves. Hygiene (ADR 0022) is about code; the text of a comment is the author's.

### Metaprograms

8. **Builtins:**

   | Builtin | Meaning |
   | --- | --- |
   | `listing ()` | the program's items in source order, followed by the comments at the end of the file |
   | `comments x` | the comments attached to `x`, in source order |
   | `doc x` | the text of the `doc` and `prose` comments leading `x`, joined by blank lines; `""` when there are none |
   | `text c`, `style c`, `place c` | a comment's text, style and place, as strings |
   | `kind x` | the kind of a syntax value, such as `"LetItem"` or `"Comment"` |
   | `with_doc s x` | a copy of the syntax `x` with a leading doc comment `s` |
   | `fail s` | stop with the error `s`, reported at the expansion site |

   A comment value can be inspected but not spliced into code: there is no code it could become. `with_doc` is the way to put documentation on generated code.
9. **Quotes keep their comments.** A comment written inside `` `( ... ) `` is attached to the quoted code, and the code the quote builds carries it, at the expansion site's location like the rest of the quote.
10. **Splices keep comments.** Spliced syntax keeps the comments attached to it. A comment attached to the splice itself, as in `` `( (** the sum *) $e ) ``, moves to the code that replaces it.
11. **Expansion keeps comments.** When expansion replaces a node, such as an operator becoming a builtin call or a top-level metaprogram call becoming the items it returns, the comments move to the replacement (the first item, for a list).

### Literate files

12. **A file ending in `.pia.md` is literate.** It is Markdown: prose by default, and code only inside fenced blocks whose info string is `pia`. Other fences, such as `ocaml` or `console`, are prose. Line and column numbers are those of the Markdown file, so diagnostics point into it.
13. **Prose becomes `prose` comments.** The prose before a code block, up to the previous block, is one comment that leads the block's first item, so it is that item's documentation even with the blank line Markdown puts before a fence. Prose after the last block is detached on the program. Code blocks are joined in order into one program, and each block must close every bracket it opens.
14. `piac --literate` reads any file as literate, and `piac --dump-ast --comments` and `--dump-expanded --comments` show the comment nodes.

## Consequences

- Programs can see their own documentation without a separate tool, and the language server can show it on hover. A metaprogram can enforce a documentation policy, or carry docs from a type to the code derived from it.
- Rendering to LaTeX and other formats (#63) still needs a metaprogram output channel that is not code, and the source spelling of a node (`source x`), which needs end positions in the syntax tree. The attachment pass already computes node extents, so this is a small step.
- A Jupyter kernel (#64) maps onto literate files directly: Markdown cells are prose, code cells are fenced `pia` blocks.
- Comments are not round-tripped byte for byte: whitespace inside them is trimmed, and a comment's exact column is not kept. A formatter would need more.
- Attachment is a heuristic. A comment between two arguments attaches to the second; a comment after a `then` on its own line leads the `then` branch. The rules are simple to state, and `--dump-ast --comments` shows the result.
- `\` reads as an escape to C programmers. It cannot be confused with one in Pia, since escapes only exist inside strings.
