#include "syntax/Interfaces.h"

#include <fstream>
#include <functional>
#include <map>
#include <optional>
#include <set>
#include <sstream>

#include "syntax/Lexer.h"
#include "syntax/Parser.h"

namespace pia::syntax {

namespace {

using K = TokenKind;
using N = NodeKind;

// The canonical text of the interface whose `interface` token is
// `tokens[first]`: its tokens up to its `end`, with a space where the
// source had any whitespace or comment between two tokens, each item of
// the signature on its own line, and `end` on a line of its own.
std::string canonical(const std::vector<Token> &tokens, size_t first) {
  std::string out;
  int depth = 0;
  const Token *prev = nullptr;
  for (size_t i = first; i < tokens.size() && tokens[i].kind != K::Eof; ++i) {
    const Token &t = tokens[i];
    if (t.kind == K::Sep) continue;
    bool closes = t.kind == K::End && depth == 1;
    if (prev) {
      if (closes)
        out += "\n";
      else if (depth == 1 && t.kind == K::Let)
        out += "\n  ";
      else if (prev->loc.offset + prev->text.size() != t.loc.offset)
        out += " ";
    }
    out += t.text;
    prev = &t;
    if (t.kind == K::Sig || t.kind == K::Struct) ++depth;
    if (t.kind == K::End && --depth == 0) break;
  }
  return out + "\n";
}

void relocate(Node &n, SourceLoc at) {
  n.loc = at;
  for (NodePtr &k : n.kids) relocate(*k, at);
}

// `a.b.c` as written: a Field chain on a Name.
std::optional<std::string> dotted(const Node &n) {
  if (n.kind == N::Name && n.flags.empty()) return n.text;
  if (n.kind != N::Field || n.kids.size() != 1) return std::nullopt;
  auto head = dotted(*n.kids[0]);
  if (!head) return std::nullopt;
  return *head + "." + n.text;
}

struct Imported {
  std::set<std::string> modules;   // `Image.Png`
  std::set<std::string> items;     // `Image.Png.decode`
};

// `M.f` in the program becomes the Name `M.f` of the imported item.
void rewrite(Node &n, const Imported &imp, Diagnostics &diags) {
  if (n.kind == N::Field) {
    if (auto d = dotted(n)) {
      if (imp.items.count(*d)) {
        n.kind = N::Name;
        n.text = *d;
        n.kids.clear();
        return;
      }
      size_t dot = d->rfind('.');
      std::string mod = d->substr(0, dot);
      if (imp.modules.count(mod)) {
        diags.error(n.loc, "the module '" + mod + "' has no '" +
                               d->substr(dot + 1) +
                               "' in the interfaces this file imports");
        return;
      }
    }
  }
  for (NodePtr &k : n.kids) rewrite(*k, imp, diags);
}

// Names of the interface's own items, inside its contracts, are its
// module's: `f` is `M.f`, unless a parameter of the item has that name.
void qualify(Node &n, const std::string &module,
             const std::set<std::string> &members,
             const std::set<std::string> &params) {
  if (n.kind == N::Name && n.flags.empty() && members.count(n.text) &&
      !params.count(n.text))
    n.text = module + "." + n.text;
  for (NodePtr &k : n.kids) qualify(*k, module, members, params);
}

// `let f : (a : t) -> (b : u) -> r requires ... ensures ...` as the
// bodyless item `let M.f (a : t) (b : u) : r requires ... ensures ...`.
NodePtr importedFunction(const Node &val, const std::string &module,
                         const std::set<std::string> &members, SourceLoc at,
                         const std::string &where, Diagnostics &diags) {
  auto item = makeNode(N::LetItem, at, module + "." + val.text);
  item->flags = "import from:" + module;
  Node *params = item->add(makeNode(N::Params, at));
  const Node *type = val.kids[0]->kids[1].get();
  std::set<std::string> names;
  for (; type->kind == N::ArrowType; type = type->kids[1].get()) {
    const Node &dom = *type->kids[0];
    if (dom.text.empty()) {
      diags.error(at, "'" + val.text + "' in " + where +
                          " has an unnamed parameter; an interface names "
                          "its parameters, as in '(x : t) -> r'");
      return nullptr;
    }
    names.insert(dom.text);
    Node *p = params->add(makeNode(N::Param, at, dom.text));
    Node *annot = p->add(makeNode(N::Annot, at));
    for (const NodePtr &k : dom.kids) annot->add(clone(*k));
    while (annot->kids.size() < 3) annot->add(makeNode(N::None, at));
  }
  if (params->kids.empty()) {
    diags.error(at, "'" + val.text + "' in " + where +
                        " is a value; importing values comes with module "
                        "state (ADR 0039, step 5)");
    return nullptr;
  }
  Node *ret = item->add(makeNode(N::RetAnnot, at));
  Node *annot = ret->add(makeNode(N::Annot, at));
  annot->add(makeNode(N::Modifiers, at));
  annot->add(clone(*type));
  annot->add(makeNode(N::None, at));
  ret->add(makeNode(N::Attrs, at));
  NodePtr contracts = clone(*val.kids[2]);
  qualify(*contracts, module, members, names);
  item->add(std::move(contracts));
  item->add(makeNode(N::Unit, at));
  relocate(*item, at);
  return item;
}

// A node's kinds and texts, as a key: two signatures with the same shape
// have the same type.
std::string shape(const Node &n) {
  std::string s = std::to_string(static_cast<int>(n.kind)) + ":" + n.text + "(";
  for (const NodePtr &k : n.kids) s += shape(*k) + ",";
  return s + ")";
}

std::optional<std::string> readFile(const std::string &path) {
  std::ifstream in(path, std::ios::binary);
  if (!in) return std::nullopt;
  std::stringstream buf;
  buf << in.rdbuf();
  return buf.str();
}

}  // namespace

std::vector<InterfaceArtifact> interfaceArtifacts(const Node &program,
                                                  std::string_view source,
                                                  bool literate,
                                                  Diagnostics &diags) {
  std::vector<InterfaceArtifact> out;
  const Node *header = nullptr;
  for (const NodePtr &item : program.kids)
    if (item->kind == N::ModuleHeader) header = item.get();
  LexOptions lex;
  lex.literate = literate;
  std::vector<Token> tokens = tokenize(source, diags, lex);
  for (const NodePtr &item : program.kids) {
    if (item->kind != N::Interface) continue;
    if (!header) {
      diags.error(item->loc, "the interface '" + item->text +
                                 "' belongs to no module: give the file a "
                                 "header, 'module M : " + item->text + "'");
      continue;
    }
    size_t first = 0;
    while (first < tokens.size() &&
           !(tokens[first].kind == K::Interface &&
             tokens[first].loc.offset == item->loc.offset))
      ++first;
    if (first == tokens.size()) {
      diags.error(item->loc, "the interface '" + item->text +
                                 "' was made by a metaprogram, so it has no "
                                 "source to publish");
      continue;
    }
    InterfaceArtifact a;
    a.module = header->text;
    a.name = item->text;
    a.text = "module " + header->text + "\n" + canonical(tokens, first);
    out.push_back(std::move(a));
  }
  return out;
}

void resolveImports(Node &program, const std::vector<std::string> &paths,
                    Diagnostics &diags) {
  std::set<std::string> theories;
  for (const NodePtr &item : program.kids)
    if (item->kind == N::Theory) theories.insert(item->text);
  Imported imp;
  std::set<std::string> seen;
  std::set<std::string> imported;  // `M.f : <shape of its type>`
  std::vector<NodePtr> out;
  bool any = false;
  for (NodePtr &item : program.kids) {
    if (item->kind != N::Import || theories.count(item->text)) {
      out.push_back(std::move(item));
      continue;
    }
    any = true;
    const std::string &path = item->text;
    SourceLoc at = item->loc;
    size_t dot = path.rfind('.');
    if (dot == std::string::npos) {
      diags.error(at, "'import " + path + "' names no interface: an import "
                      "names one interface of a module, as in 'import " +
                      path + ".I'");
      continue;
    }
    if (!seen.insert(path).second) {
      diags.error(at, "'" + path + "' is already imported");
      continue;
    }
    std::string module = path.substr(0, dot), name = path.substr(dot + 1);
    std::string file = path + ".piai", found;
    std::optional<std::string> text;
    for (const std::string &dir : paths) {
      found = dir.empty() ? file : dir + "/" + file;
      if ((text = readFile(found))) break;
    }
    if (!text) {
      diags.error(at, "no interface artifact '" + file +
                      "' on the interface path; make it with 'piac "
                      "--emit=interface' and pass its directory with "
                      "--iface-path");
      continue;
    }
    Diagnostics parsed;
    NodePtr artifact = parseProgram(*text, parsed);
    const Node *iface = nullptr, *header = nullptr;
    if (!parsed.hasErrors() && artifact->kids.size() == 2) {
      header = artifact->kids[0].get();
      iface = artifact->kids[1].get();
    }
    if (!header || header->kind != N::ModuleHeader ||
        iface->kind != N::Interface) {
      std::string why = parsed.hasErrors() ? ": " + parsed.errors()[0].message
                                           : "";
      diags.error(at, "'" + found + "' is not an interface artifact" + why);
      continue;
    }
    if (header->text != module || iface->text != name) {
      diags.error(at, "'" + found + "' holds '" + header->text + "." +
                      iface->text + "', not '" + path + "'");
      continue;
    }
    std::string where = "'" + path + "'";
    std::set<std::string> members;
    for (const NodePtr &k : iface->kids)
      if (k->kind == N::SigVal || k->kind == N::SigType)
        members.insert(k->text);
    std::set<std::string> listed;
    for (const NodePtr &k : iface->kids) {
      if (k->kind == N::Attrs || k->kind == N::Comment) continue;
      if (k->kind != N::SigVal) {
        diags.error(at, "importing the type '" + k->text + "' from " + where +
                        " is not supported yet: imports bring in functions "
                        "of builtin types, and types follow in ADR 0039 "
                        "step 3");
        continue;
      }
      // An overload set comes in whole: each overload is its own bodyless
      // item, told apart by its parameter types (ADR 0034), so the calls
      // resolve and link as they do in the defining module.
      std::string sig = shape(*k->kids[0]);
      if (!listed.insert(k->text + " : " + sig).second) {
        diags.error(at, "'" + k->text + "' is listed twice in " + where +
                        " with the same type");
        continue;
      }
      std::string qualified = module + "." + k->text;
      // Two interfaces of one module may list the same function.
      if (!imported.insert(qualified + " : " + sig).second) continue;
      NodePtr fn = importedFunction(*k, module, members, at, where, diags);
      if (!fn) continue;
      imp.items.insert(qualified);
      out.push_back(std::move(fn));
    }
    imp.modules.insert(module);
  }
  program.kids = std::move(out);
  if (any) rewrite(program, imp, diags);
}

}  // namespace pia::syntax
