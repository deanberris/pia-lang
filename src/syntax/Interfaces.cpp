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
      // A `let` that starts an item, not a generic type's `let (t : type)`.
      else if (depth == 1 && t.kind == K::Let &&
               !(i + 1 < tokens.size() && tokens[i + 1].kind == K::LParen))
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
  std::set<std::string> types;     // `Image.Png.pixel`
  std::set<std::string> ctors;     // `Image.Png.Truncated`
  std::map<std::string, std::string> aliases;      // `Png` -> `Image.Png`
  std::map<std::string, std::string> unqualified;  // `decode` -> `Image.Png.decode`
};

// `Png.decode` as `Image.Png.decode`, under `import Image.Png.Codec as Png`.
std::string unalias(const std::string &d, const Imported &imp) {
  for (const auto &[alias, module] : imp.aliases)
    if (d.size() > alias.size() && d.compare(0, alias.size(), alias) == 0 &&
        d[alias.size()] == '.')
      return module + d.substr(alias.size());
  return d;
}

// The names a program binds anywhere: its items, parameters and pattern
// variables, which an unqualified import must not shadow (ADR 0022).
void bindersIn(const Node &n, std::set<std::string> &out) {
  if (n.kind == N::Param || n.kind == N::PVar || n.kind == N::LetItem)
    out.insert(n.text);
  for (const NodePtr &k : n.kids) bindersIn(*k, out);
}

void collectCtors(const Node &n, const std::string &module,
                  std::set<std::string> &out) {
  if (n.kind == N::Ctor) out.insert(module + "." + n.text);
  for (const NodePtr &k : n.kids) collectCtors(*k, module, out);
}

// `M.f` in the program becomes the Name `M.f` of the imported item.
// In an imported definition, such as a generic function's body or a
// concept's signature, `M.f` naming an item of another imported module,
// such as the concept `Pia.Core.Order.Eq` that a generic of
// Pia.Core.Algo.Search is constrained by. Nothing else is renamed: the
// importer's own unqualified names must not capture the definition's.
void resolveDotted(Node &n, const Imported &imp) {
  if (n.kind == N::Field)
    if (auto d = dotted(n)) {
      std::string name = unalias(*d, imp);
      if (imp.items.count(name)) {
        n.kind = N::Name;
        n.text = name;
        n.kids.clear();
        return;
      }
    }
  for (NodePtr &k : n.kids) resolveDotted(*k, imp);
}

void rewrite(Node &n, const Imported &imp, Diagnostics &diags) {
  if (n.kind == N::TypeName || n.kind == N::TypeInst ||
      n.kind == N::SigInclude) {
    n.text = unalias(n.text, imp);
    if (auto u = imp.unqualified.find(n.text); u != imp.unqualified.end())
      n.text = u->second;
  }
  if (n.kind == N::Name && n.flags.empty())
    if (auto u = imp.unqualified.find(n.text); u != imp.unqualified.end()) {
      n.text = u->second;
      return;
    }
  if (n.kind == N::Field) {
    if (auto d = dotted(n)) {
      *d = unalias(*d, imp);
      if (imp.items.count(*d)) {
        n.kind = N::Name;
        n.text = *d;
        n.kids.clear();
        return;
      }
      // `M.C` is the constructor `C`, which is also in scope as `C`.
      if (imp.ctors.count(*d)) {
        n.kind = N::Name;
        n.text = d->substr(d->rfind('.') + 1);
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
// The same for the types it shows, in types and contracts, except a
// generic type's own parameters.
void qualify(Node &n, const std::string &module,
             const std::set<std::string> &members,
             const std::set<std::string> &params,
             const std::set<std::string> &typeParams = {}) {
  if (n.kind == N::Name && n.flags.empty() && members.count(n.text) &&
      !params.count(n.text))
    n.text = module + "." + n.text;
  if ((n.kind == N::TypeName || n.kind == N::TypeInst ||
       n.kind == N::SigInclude) &&
      members.count(n.text) && !typeParams.count(n.text))
    n.text = module + "." + n.text;
  for (NodePtr &k : n.kids) qualify(*k, module, members, params, typeParams);
}

// `let t = type ...` or `let t = let (a : type) => type ...` as the type
// item `M.t`, whose constructors keep their names: they are reachable
// unqualified, and a clash with another constructor is an error, as for
// any two constructors (ADR 0039).
NodePtr importedType(const Node &shown, const std::string &module,
                     const std::set<std::string> &members, SourceLoc at) {
  auto item = makeNode(N::LetItem, at, module + "." + shown.text);
  item->add(makeNode(N::Params, at));
  item->add(makeNode(N::None, at));
  item->add(makeNode(N::Contracts, at));
  NodePtr value = clone(*shown.kids[0]);
  std::set<std::string> typeParams;
  if (value->kind == N::Lambda)
    for (const NodePtr &p : value->kids)
      if (p->kind == N::LParam && !p->kids.empty() &&
          p->kids[0]->kind == N::PVar)
        typeParams.insert(p->kids[0]->text);
  qualify(*value, module, members, {}, typeParams);
  item->add(std::move(value));
  relocate(*item, at);
  return item;
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
  // A value, `let n : u32`, is a function of no parameters to its
  // importers. State, `let count : fixed u32`, comes with step 5.
  if (params->kids.empty() && !val.kids[0]->kids[0]->text.empty()) {
    diags.error(at, "'" + val.text + "' in " + where +
                        " is module state; importing state is not supported "
                        "yet (ADR 0039, step 5)");
    return nullptr;
  }
  Node *ret = item->add(makeNode(N::RetAnnot, at));
  Node *annot = ret->add(makeNode(N::Annot, at));
  annot->add(makeNode(N::Modifiers, at));
  annot->add(clone(*type));
  annot->add(makeNode(N::None, at));
  ret->add(makeNode(N::Attrs, at));
  qualify(*params, module, members, names);
  qualify(*ret, module, members, names);
  NodePtr contracts = clone(*val.kids[2]);
  qualify(*contracts, module, members, names);
  item->add(std::move(contracts));
  // A shown value, `let n : u32 = 4096`, comes with its definition, which
  // importers' proofs and code use; there is nothing to link.
  if (params->kids.empty() && val.kids.size() > 3) {
    item->flags = "from:" + module;
    NodePtr value = clone(*val.kids[3]);
    qualify(*value, module, members, names);
    item->add(std::move(value));
  } else {
    item->add(makeNode(N::Unit, at));
  }
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

// Whether a sig entry's type takes a type parameter, `(t : type) -> ...`.
bool genericSig(const Node &val) {
  for (const Node *cur = val.kids[0]->kids[1].get(); cur->kind == N::ArrowType;
       cur = cur->kids[1].get())
    if (cur->kids[0]->kids.size() > 1 &&
        cur->kids[0]->kids[1]->kind == N::TypeKind)
      return true;
  return false;
}

// Whether an item is a generic function, `let f (t : type) ...`.
bool genericItem(const Node &item) {
  if (item.kind != N::LetItem || item.kids.empty()) return false;
  for (const NodePtr &p : item.kids[0]->kids)
    if (p->kind == N::Param && !p->kids.empty() &&
        p->kids[0]->kids.size() > 1 && p->kids[0]->kids[1]->kind == N::TypeKind)
      return true;
  return false;
}

bool hasWord(const std::string &flags, const std::string &word) {
  std::istringstream in(flags);
  std::string w;
  while (in >> w)
    if (w == word) return true;
  return false;
}

// Whether an item is a concept, `let meta C (t : type) : concept = sig`.
bool conceptItem(const Node &item) {
  return item.kind == N::LetItem && hasWord(item.flags, "meta") &&
         item.kids.size() > 3 && item.kids[3]->kind == N::Sig;
}

// Whether an item is a spec function, `let spec f ...`.
bool specItem(const Node &item) {
  return item.kind == N::LetItem && hasWord(item.flags, "spec");
}

// Whether a sig entry is exported with its definition: a concept, a spec
// function or a generic function (ADR 0039).
bool inlinedSig(const Node &k) {
  return k.kind == N::SigVal &&
         (k.flags == "meta" || k.flags == "spec" || genericSig(k));
}

bool inlinedItem(const Node &item) {
  return genericItem(item) || conceptItem(item) || specItem(item);
}

// The names an item uses, as names and as types.
void namesIn(const Node &n, std::set<std::string> &out) {
  if ((n.kind == N::Name && n.flags.empty()) || n.kind == N::TypeName ||
      n.kind == N::TypeInst || n.kind == N::SigInclude)
    out.insert(n.text);
  for (const NodePtr &k : n.kids) namesIn(*k, out);
}

// The canonical text of a top-level item: its tokens from `start` up to
// `end`, on one line.
std::string canonicalItem(const std::vector<Token> &tokens, uint32_t start,
                          uint32_t end) {
  std::string out;
  const Token *prev = nullptr;
  for (const Token &t : tokens) {
    if (t.kind == K::Eof || t.loc.offset >= end) break;
    if (t.loc.offset < start || t.kind == K::Sep) continue;
    if (prev && prev->loc.offset + prev->text.size() != t.loc.offset)
      out += " ";
    out += t.text;
    prev = &t;
  }
  return out + "\n";
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
    // Generic functions and concepts are exported with their definitions,
    // which importers instantiate and run (ADR 0039): the inline surface.
    std::set<std::string> listed, inlined;
    for (const NodePtr &k : item->kids)
      if (k->kind == N::SigVal || k->kind == N::SigType) {
        listed.insert(k->text);
        if (inlinedSig(*k)) inlined.insert(k->text);
      }
    std::set<std::string> topLevel;
    for (const NodePtr &other : program.kids)
      if (other->kind == N::LetItem) topLevel.insert(other->text);
    for (size_t i = 0; i < program.kids.size(); ++i) {
      const Node &def = *program.kids[i];
      if (!inlined.count(def.text) || !inlinedItem(def)) continue;
      std::set<std::string> uses;
      namesIn(def, uses);
      for (const std::string &u : uses)
        if (u != def.text && topLevel.count(u) && !listed.count(u))
          diags.error(def.loc, "'" + def.text + "' is exported with its "
                               "definition, which uses '" + u + "', which "
                               "the interface '" + item->text +
                               "' does not list");
      uint32_t end = i + 1 < program.kids.size()
                         ? program.kids[i + 1]->loc.offset
                         : static_cast<uint32_t>(source.size());
      a.text += canonicalItem(tokens, def.loc.offset, end);
    }
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
  // The program's own items, which `as` and `{ }` apply to; imported
  // items name things as their own module does.
  std::set<const Node *> own;
  std::set<std::string> binders;
  bindersIn(program, binders);
  for (NodePtr &item : program.kids) {
    if (item->kind != N::Import || theories.count(item->text)) {
      own.insert(item.get());
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
    if (!parsed.hasErrors() && artifact->kids.size() >= 2) {
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
    // Shown types and concepts, which an inlined definition names through
    // the module; its calls find the module's functions by their own
    // names, as in the module (ADR 0039, section 6).
    std::set<std::string> typesAndConcepts, inlined;
    for (const NodePtr &k : iface->kids) {
      // Spec functions are named through the module too: they are not
      // overloaded, so the name finds the one definition.
      if (k->kind == N::SigType ||
          (k->kind == N::SigVal && (k->flags == "meta" || k->flags == "spec")))
        typesAndConcepts.insert(k->text);
      if (inlinedSig(*k)) inlined.insert(k->text);
    }
    std::set<std::string> listed;
    for (const NodePtr &k : iface->kids) {
      if (k->kind == N::Attrs || k->kind == N::Comment) continue;
      // A generic function or a concept comes in with its definition,
      // below.
      if (k->kind == N::SigVal && inlined.count(k->text)) {
        imp.items.insert(module + "." + k->text);
        continue;
      }
      if (k->kind == N::SigType) {
        std::string qualified = module + "." + k->text;
        // Two interfaces of one module may show the same type.
        if (!imp.types.insert(qualified).second) continue;
        collectCtors(*k, module, imp.ctors);
        out.push_back(importedType(*k, module, members, at));
        continue;
      }
      if (k->kind != N::SigVal) {
        diags.error(at, "importing '" + k->text + "' from " + where +
                        " is not supported yet");
        continue;
      }
      if (k->kids[0]->kids[1]->kind == N::TypeKind) {
        diags.error(at, "importing the abstract type '" + k->text +
                        "' from " + where + " is not supported yet: show "
                        "its definition with '=' (ADR 0039, step 3)");
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
    for (size_t i = 2; i < artifact->kids.size(); ++i) {
      const Node &def = *artifact->kids[i];
      if (def.kind == N::Comment) continue;
      if (def.kind != N::LetItem || !inlined.count(def.text) ||
          !inlinedItem(def)) {
        diags.error(at, "'" + found + "' is not an interface artifact: it "
                        "defines '" + def.text + "', which is not a generic "
                        "function, spec function or concept the interface "
                        "lists");
        continue;
      }
      NodePtr copy = clone(def);
      copy->text = module + "." + def.text;
      copy->flags += copy->flags.empty() ? "from:" + module : " from:" + module;
      if (!imported.insert(copy->text + " = " + shape(*copy)).second) continue;
      // Parameters keep their names; no binding shadows a member, since
      // Pia has no shadowing.
      std::set<std::string> params;
      for (const NodePtr &p : copy->kids[0]->kids)
        if (p->kind == N::Param) params.insert(p->text);
      qualify(*copy, module, typesAndConcepts, params, params);
      relocate(*copy, at);
      out.push_back(std::move(copy));
    }
    imp.modules.insert(module);
    for (const NodePtr &k : item->kids) {
      if (k->kind != N::Name) continue;
      if (k->flags == "as") {
        if (binders.count(k->text) || imp.aliases.count(k->text) ||
            imp.unqualified.count(k->text))
          diags.error(k->loc, "'" + k->text + "' is already a name in this "
                              "file, so it cannot also name the module '" +
                              module + "'");
        else
          imp.aliases[k->text] = module;
        continue;
      }
      if (!members.count(k->text)) {
        diags.error(k->loc, "the interface " + where + " has no '" +
                            k->text + "'");
        continue;
      }
      std::string qualified = module + "." + k->text;
      auto prior = imp.unqualified.find(k->text);
      if (prior != imp.unqualified.end() && prior->second == qualified)
        continue;  // two interfaces of one module may list it
      if (binders.count(k->text) || prior != imp.unqualified.end() ||
          imp.aliases.count(k->text))
        diags.error(k->loc, "importing '" + k->text + "' unqualified would "
                            "shadow " + (prior != imp.unqualified.end()
                                             ? "'" + prior->second + "'"
                                             : "a name this file binds") +
                            "; use '" + qualified + "' instead (ADR 0022)");
      else
        imp.unqualified[k->text] = qualified;
    }
  }
  program.kids = std::move(out);
  if (any)
    for (NodePtr &item : program.kids) {
      if (own.count(item.get()))
        rewrite(*item, imp, diags);
      else
        resolveDotted(*item, imp);
    }
}

}  // namespace pia::syntax
