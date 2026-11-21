#include "repl/Session.h"

#include <algorithm>
#include <cctype>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <map>
#include <optional>
#include <set>
#include <sstream>

#include "codegen/Codegen.h"
#include "dialect/PiaDialect.h"
#include "irgen/IRGen.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/TargetParser/Host.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/ExecutionEngine/ExecutionEngine.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/MLIRContext.h"
#include "sema/Sema.h"
#include "syntax/Lexer.h"
#include "syntax/Parser.h"
#include "verify/Verifier.h"

namespace pia::repl {

using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;

namespace {

constexpr const char *kFile = "<repl>";
constexpr const char *kEvalPrefix = "__pia_eval_";

std::string trim(std::string_view s) {
  size_t b = 0, e = s.size();
  while (b < e && std::isspace(static_cast<unsigned char>(s[b]))) ++b;
  while (e > b && std::isspace(static_cast<unsigned char>(s[e - 1]))) --e;
  return std::string(s.substr(b, e - b));
}

std::string trimRight(std::string_view s) {
  size_t e = s.size();
  while (e > 0 && std::isspace(static_cast<unsigned char>(s[e - 1]))) --e;
  return std::string(s.substr(0, e));
}

unsigned countLines(std::string_view s) {
  unsigned n = 0;
  for (char c : s) n += c == '\n';
  return n;
}

std::string plural(size_t n, const char *word) {
  return std::to_string(n) + " " + word + (n == 1 ? "" : "s");
}

// "[3]:2:5", the way locations inside cells are written.
std::string formatWhere(const Where &w) {
  if (w.cell == 0) return "";
  std::string out = "[" + std::to_string(w.cell) + "]";
  if (w.line) out += ":" + std::to_string(w.line);
  if (w.column) out += ":" + std::to_string(w.column);
  return out;
}

// The C name of a function's entry point (docs/codegen.md, "C ABI").
std::string cName(const std::string &name) {
  std::string out;
  for (char c : name) out += c == '\'' ? std::string("_prime") : std::string(1, c);
  return out;
}

// One definition in the environment: the text of a top-level item, kept as
// the user wrote it so the environment can be parsed again with each cell.
struct Entry {
  unsigned cell = 0;
  unsigned line = 1;       // the item's first line within its cell
  std::string source;      // the item, without trailing whitespace
  std::string kind;        // "let", "type", "meta", "operator", "expansion"
  std::string head;        // the name it was written with, if any
  std::vector<std::string> names;  // what it defines, after expansion
};

// Where a stretch of the combined source came from.
struct Segment {
  uint32_t offset = 0, end = 0;  // byte range in the combined source
  unsigned vline = 1;            // its first line there
  unsigned cell = 0, line = 1;   // and in its cell
  int entry = -1;                // index into the env, or -1 for the cell
};

// A function's type as Pia writes it: `(a : u8) -> (b : u8) -> u8`, or the
// result type alone for a constant.
std::string functionType(mlir::func::FuncOp fn) {
  mlir::FunctionType t = fn.getFunctionType();
  std::string out;
  for (unsigned i = 0; i < t.getNumInputs(); ++i) {
    std::string name;
    if (auto nl = mlir::dyn_cast<mlir::NameLoc>(fn.getArgument(i).getLoc()))
      name = nl.getName().str();
    std::string mods;
    if (auto a = fn.getArgAttrOfType<mlir::StringAttr>(
            i, PiaDialect::getModifiersAttrName()))
      mods = a.getValue().str() + " ";
    out += "(" + (name.empty() ? std::string("_") : name) + " : " + mods +
           sema::typeName(t.getInput(i)) + ") -> ";
  }
  out += t.getNumResults() ? sema::typeName(t.getResult(0)) : "unit";
  return out;
}

// The C layout of a record result: each field at its natural offset.
struct Layout {
  size_t size = 0, align = 1;
};

std::optional<Layout> layoutOf(mlir::Type t) {
  if (t.isInteger(1)) return Layout{1, 1};
  if (auto it = mlir::dyn_cast<IntType>(t)) {
    size_t bytes = it.getStorageWidth() / 8;
    return Layout{bytes, bytes};
  }
  if (auto r = mlir::dyn_cast<RecordType>(t)) {
    Layout l;
    for (mlir::Type f : r.getFieldTypes()) {
      std::optional<Layout> fl = layoutOf(f);
      if (!fl) return std::nullopt;
      l.size = (l.size + fl->align - 1) / fl->align * fl->align + fl->size;
      l.align = std::max(l.align, fl->align);
    }
    l.size = (l.size + l.align - 1) / l.align * l.align;
    return l;
  }
  return std::nullopt;
}

std::string formatInt(IntType it, const unsigned char *p) {
  unsigned bytes = it.getStorageWidth() / 8;
  bool isSigned = it.getLo().isNegative();
  uint64_t u = 0;
  std::memcpy(&u, p, bytes);  // little endian, like every target Pia has
  if (!isSigned) return std::to_string(u);
  unsigned bits = bytes * 8;
  int64_t s = bits == 64 ? static_cast<int64_t>(u)
                         : static_cast<int64_t>(u << (64 - bits)) >> (64 - bits);
  return std::to_string(s);
}

// Formats the value of type `t` stored at `p` in C layout.
std::string formatValue(mlir::Type t, const unsigned char *p) {
  if (t.isInteger(1)) return *p ? "true" : "false";
  if (auto it = mlir::dyn_cast<IntType>(t)) return formatInt(it, p);
  auto r = mlir::cast<RecordType>(t);
  std::string out = "{ ";
  size_t offset = 0;
  for (size_t i = 0; i < r.getFieldTypes().size(); ++i) {
    mlir::Type f = r.getFieldTypes()[i];
    Layout fl = *layoutOf(f);
    offset = (offset + fl.align - 1) / fl.align * fl.align;
    if (i) out += "; ";
    out += r.getFieldNames()[i].getValue().str() + " = " +
           formatValue(f, p + offset);
    offset += fl.size;
  }
  return out + " }";
}

// Calls a JIT-compiled C entry point that takes no arguments and returns a
// value of type `t` (null for unit), and formats the result.
std::string callAndFormat(void *fp, mlir::Type t) {
  if (!t) {
    reinterpret_cast<void (*)()>(fp)();
    return "()";
  }
  if (t.isInteger(1)) return reinterpret_cast<bool (*)()>(fp)() ? "true" : "false";
  if (auto it = mlir::dyn_cast<IntType>(t)) {
    unsigned char buf[8] = {0};
    bool s = it.getLo().isNegative();
    auto store = [&](auto v) { std::memcpy(buf, &v, sizeof v); };
    switch (it.getStorageWidth()) {
      case 8: s ? store(reinterpret_cast<int8_t (*)()>(fp)())
                : store(reinterpret_cast<uint8_t (*)()>(fp)()); break;
      case 16: s ? store(reinterpret_cast<int16_t (*)()>(fp)())
                 : store(reinterpret_cast<uint16_t (*)()>(fp)()); break;
      case 32: s ? store(reinterpret_cast<int32_t (*)()>(fp)())
                 : store(reinterpret_cast<uint32_t (*)()>(fp)()); break;
      default: s ? store(reinterpret_cast<int64_t (*)()>(fp)())
                 : store(reinterpret_cast<uint64_t (*)()>(fp)()); break;
    }
    return formatInt(it, buf);
  }
  // A record comes back through a pointer to a C struct of its fields.
  Layout l = *layoutOf(t);
  std::vector<uint64_t> storage(l.size / 8 + 1, 0);
  reinterpret_cast<void (*)(void *)>(fp)(storage.data());
  return formatValue(t, reinterpret_cast<const unsigned char *>(storage.data()));
}

bool showable(mlir::Type t) { return !t || layoutOf(t).has_value(); }

// The names of the top-level functions that `n` refers to.
void collectRefs(const Node &n, std::set<std::string> &out) {
  if (n.kind == NodeKind::Name) out.insert(n.text);
  for (const NodePtr &k : n.kids) collectRefs(*k, out);
}

const char *helpText =
    "Enter Pia code to define things or evaluate expressions, or a command:\n"
    "  :type <expr>      show an expression's type (or a definition's)\n"
    "  :proof [<name>]   show the obligations of a definition, or a summary\n"
    "  :env              list the environment's definitions\n"
    "  :source <name>    show a definition's source\n"
    "  :redef <code>     replace definitions of the same names\n"
    "  :forget <name>    remove a definition nothing else uses\n"
    "  :allow [<spec>]   accept unproved obligations in a function or at\n"
    "                    [cell]:line[:col], like piac --allow-unproved\n"
    "  :load <file>      run a file as one cell\n"
    "  :reset            empty the environment\n"
    "  :help             this list\n"
    "  :quit             leave\n"
    "A definition joins the environment only if everything still verifies.\n";

}  // namespace

struct Session::Impl {
  Options options;
  mlir::MLIRContext ctx;
  std::vector<Entry> env;
  unsigned cells = 0;
  // The obligations of each function, from the last cell that committed.
  std::map<std::string, std::vector<Event>> proofs;
  std::map<std::string, std::string> types;  // name -> type, as shown

  explicit Impl(Options o) : options(std::move(o)) {
    irgen::loadDialects(ctx);
    codegen::loadDialects(ctx);
    static bool targets = [] {
      llvm::InitializeNativeTarget();
      llvm::InitializeNativeTargetAsmPrinter();
      return true;
    }();
    (void)targets;
  }

  // ---- one attempt at the environment plus a cell ----------------------

  enum class Mode { Define, Redefine, Type, Check };

  struct Attempt {
    std::string source;
    std::vector<Segment> segments;
    uint32_t cellOffset = 0;
    std::vector<Event> errors;
    NodePtr tree;
  };

  Where where(const Attempt &a, unsigned vline, unsigned column) const {
    for (const Segment &s : a.segments)
      if (vline >= s.vline &&
          vline < s.vline + countLines(std::string_view(a.source).substr(
                                s.offset, s.end - s.offset)))
        return Where{s.cell, s.line + (vline - s.vline), column};
    return Where{};
  }

  Where whereOf(const Attempt &a, const std::string &loc) const {
    // "<repl>:line:col"
    size_t c = loc.rfind(':');
    if (c == std::string::npos || c == 0) return Where{};
    size_t l = loc.rfind(':', c - 1);
    if (l == std::string::npos) return Where{};
    unsigned line = std::strtoul(loc.c_str() + l + 1, nullptr, 10);
    unsigned col = std::strtoul(loc.c_str() + c + 1, nullptr, 10);
    return where(a, line, col);
  }

  const Segment *segmentAt(const Attempt &a, uint32_t offset) const {
    for (const Segment &s : a.segments)
      if (offset >= s.offset && offset < s.end) return &s;
    return nullptr;
  }

  void error(std::vector<Event> &out, std::string text, Where w = {}) {
    Event e;
    e.kind = Event::Kind::Error;
    e.text = std::move(text);
    e.where = w;
    out.push_back(std::move(e));
  }

  void takeDiagnostics(Attempt &a, const syntax::Diagnostics &d) {
    for (const syntax::Diagnostic &x : d.errors())
      error(a.errors, x.message, where(a, x.loc.line, x.loc.column));
  }

  // Joins `entries` and `cell` into one program and parses it.
  Attempt parse(const std::vector<Entry> &entries, std::string_view cell,
                unsigned cellNo) {
    Attempt a;
    for (size_t i = 0; i < entries.size(); ++i) {
      Segment s;
      s.offset = a.source.size();
      s.vline = countLines(a.source) + 1;
      s.cell = entries[i].cell;
      s.line = entries[i].line;
      s.entry = static_cast<int>(i);
      a.source += entries[i].source;
      a.source += "\n";
      s.end = a.source.size();
      a.segments.push_back(s);
    }
    Segment s;
    s.offset = a.cellOffset = a.source.size();
    s.vline = countLines(a.source) + 1;
    s.cell = cellNo;
    a.source += cell;
    a.source += "\n";
    s.end = a.source.size();
    a.segments.push_back(s);

    syntax::Diagnostics d;
    a.tree = syntax::parseProgram(a.source, d);
    takeDiagnostics(a, d);
    return a;
  }

  // ---- cells -------------------------------------------------------------

  CellResult code(std::string_view text, Mode mode, unsigned cellNo,
                  std::vector<std::string> forgotten = {}) {
    CellResult r;
    r.cell = cellNo;
    std::vector<Entry> base = env;

    // Parse once to learn what the cell defines, and take out what a
    // redefinition replaces.
    Attempt a = parse(base, text, cellNo);
    if (!a.errors.empty()) return fail(r, std::move(a.errors));

    struct Item {
      Entry entry;
      NodeKind kind;
      uint32_t offset;
    };
    std::vector<Item> items;
    for (size_t i = 0; i < a.tree->kids.size(); ++i) {
      const Node &k = *a.tree->kids[i];
      if (k.loc.offset < a.cellOffset) continue;
      uint32_t end = i + 1 < a.tree->kids.size()
                         ? a.tree->kids[i + 1]->loc.offset
                         : static_cast<uint32_t>(a.source.size());
      Item it;
      it.kind = k.kind;
      it.offset = k.loc.offset;
      it.entry.cell = cellNo;
      it.entry.line = where(a, k.loc.line, k.loc.column).line;
      it.entry.source =
          trimRight(std::string_view(a.source).substr(k.loc.offset,
                                                       end - k.loc.offset));
      if (k.kind == NodeKind::LetItem) {
        it.entry.head = k.text;
        it.entry.kind = k.flags.find("meta") != std::string::npos ? "meta"
                        : sema::isTypeItem(k)                     ? "type"
                                                                  : "let";
      } else if (k.kind == NodeKind::MetaOperator) {
        it.entry.head = "(" + k.text + ")";
        it.entry.kind = "operator";
      } else if (k.kind == NodeKind::ExprItem) {
        it.entry.kind = "expansion";  // until we know it is an expression
      } else {
        it.entry.kind = "item";
      }
      items.push_back(std::move(it));
    }
    if (items.empty() && mode != Mode::Check && mode != Mode::Type)
      return r;  // only comments

    std::vector<std::string> replaced;
    for (const Item &it : items) {
      if (it.entry.head.empty()) continue;
      int owner = ownerOf(base, it.entry.head);
      if (owner < 0) {
        if (mode == Mode::Redefine) {
          error(r.events, "there is no '" + it.entry.head + "' to redefine",
                Where{cellNo, it.entry.line, 1});
          r.ok = false;
        }
        continue;
      }
      const Entry &old = base[owner];
      if (mode != Mode::Redefine) {
        error(r.events,
              "'" + it.entry.head + "' is already defined in cell [" +
                  std::to_string(old.cell) +
                  "]; Pia does not allow shadowing (ADR 0022), so name it " +
                  it.entry.head + "' or replace it with :redef",
              Where{cellNo, it.entry.line, 1});
        r.ok = false;
      } else if (old.kind == "expansion") {
        error(r.events,
              "'" + it.entry.head + "' was generated by a metaprogram in cell [" +
                  std::to_string(old.cell) + "]; redefine that instead",
              Where{cellNo, it.entry.line, 1});
        r.ok = false;
      } else {
        replaced.push_back(it.entry.head);
        base.erase(base.begin() + owner);
      }
    }
    if (!r.ok) return r;
    if (!replaced.empty()) {
      a = parse(base, text, cellNo);
      if (!a.errors.empty()) return fail(r, std::move(a.errors));
    }

    // Run the metaprograms, then see who defines what.
    syntax::Diagnostics d;
    meta::expand(*a.tree, d, options.meta);
    takeDiagnostics(a, d);
    if (!a.errors.empty()) return fail(r, std::move(a.errors));

    std::map<int, std::vector<std::string>> envNames;  // entry -> names
    std::vector<std::string> cellNames;
    std::set<uint32_t> exprOffsets;
    std::vector<std::pair<std::string, mlir::Type>> evals;
    unsigned evalCount = 0;
    for (Item &it : items)
      if (!it.entry.head.empty()) it.entry.names = {it.entry.head};
    // The cell item a generated definition came from: the last one that
    // starts at or before its location (the expansion site).
    auto cellItemAt = [&](uint32_t offset) -> Item * {
      Item *best = nullptr;
      for (Item &it : items)
        if (it.offset <= offset) best = &it;
      return best;
    };
    for (NodePtr &k : a.tree->kids) {
      const Segment *s = segmentAt(a, k->loc.offset);
      if (k->kind == NodeKind::ExprItem && s && s->entry < 0) {
        // An expression to evaluate: wrap it in a constant.
        exprOffsets.insert(k->loc.offset);
        NodePtr let = syntax::makeNode(NodeKind::LetItem, k->loc,
                                       kEvalPrefix + std::to_string(cellNo) +
                                           "_" + std::to_string(++evalCount));
        let->add(syntax::makeNode(NodeKind::Params, k->loc));
        let->add(syntax::makeNode(NodeKind::None, k->loc));
        let->add(syntax::makeNode(NodeKind::Contracts, k->loc));
        let->add(std::move(k->kids[0]));
        evals.emplace_back(let->text, mlir::Type());
        k = std::move(let);
        continue;
      }
      if (k->kind != NodeKind::LetItem || !s) continue;
      if (s->entry >= 0) {
        envNames[s->entry].push_back(k->text);
        continue;
      }
      cellNames.push_back(k->text);
      if (Item *it = cellItemAt(k->loc.offset))
        if (std::find(it->entry.names.begin(), it->entry.names.end(), k->text) ==
            it->entry.names.end())
          it->entry.names.push_back(k->text);
    }
    for (Item &it : items)
      if (it.kind == NodeKind::ExprItem && exprOffsets.count(it.offset))
        it.entry.kind = "expression";
    // What each older definition defines now: a metaprogram it calls may
    // generate different names than it did.
    for (size_t i = 0; i < base.size(); ++i) {
      std::vector<std::string> names;
      if (!base[i].head.empty()) names.push_back(base[i].head);
      for (const std::string &n : envNames[static_cast<int>(i)])
        if (std::find(names.begin(), names.end(), n) == names.end())
          names.push_back(n);
      base[i].names = std::move(names);
    }
    for (const Item &it : items)
      for (const std::string &n : it.entry.names) {
        if (n == it.entry.head) continue;  // checked above
        int owner = ownerOf(base, n);
        if (owner < 0) continue;
        error(r.events,
              "'" + n + "' is already defined in cell [" +
                  std::to_string(base[owner].cell) +
                  "]; Pia does not allow shadowing (ADR 0022), so name it " +
                  n + "' or replace it with :redef",
              Where{cellNo, it.entry.line, 1});
        r.ok = false;
      }
    if (!r.ok) return r;

    // Lower the whole environment and the cell, capturing MLIR's own
    // diagnostics too.
    std::vector<Event> mlirErrors;
    mlir::ScopedDiagnosticHandler handler(&ctx, [&](mlir::Diagnostic &diag) {
      if (diag.getSeverity() == mlir::DiagnosticSeverity::Error)
        error(mlirErrors, diag.str(),
              whereOf(a, verify::formatLoc(diag.getLocation())));
      return mlir::success();
    });
    syntax::Diagnostics gd;
    mlir::OwningOpRef<mlir::ModuleOp> module =
        irgen::generate(*a.tree, kFile, ctx, gd);
    takeDiagnostics(a, gd);
    for (Event &e : mlirErrors) a.errors.push_back(std::move(e));
    mlirErrors.clear();
    if (!a.errors.empty()) {
      std::vector<std::string> changed = replaced;
      changed.insert(changed.end(), forgotten.begin(), forgotten.end());
      noteDependents(a, r, changed);
      return fail(r, std::move(a.errors));
    }
    if (!module) {
      error(r.events, "internal error: the generated IR does not verify");
      r.ok = false;
      return r;
    }

    std::map<std::string, mlir::func::FuncOp> fns;
    module->walk([&](mlir::func::FuncOp f) { fns[f.getSymName().str()] = f; });
    std::map<std::string, std::string> newTypes;
    std::map<std::string, mlir::Type> results;
    for (auto &[name, f] : fns) {
      newTypes[name] = functionType(f);
      mlir::FunctionType t = f.getFunctionType();
      results[name] = t.getNumResults() ? t.getResult(0) : mlir::Type();
    }
    for (auto &[name, t] : evals) t = results[name];

    if (mode == Mode::Type) {
      for (auto &[name, t] : evals) {
        Event e;
        e.kind = Event::Kind::Type;
        e.text = trim(text);
        e.type = t ? sema::typeName(t) : "unit";
        r.events.push_back(std::move(e));
      }
      return r;
    }

    // Verify everything. The environment verified before, so whatever fails
    // now comes from this cell, or from a definition it replaced.
    std::set<std::string> mine(cellNames.begin(), cellNames.end());
    for (auto &[name, t] : evals) mine.insert(name);
    verify::Options vo;
    vo.timeoutMs = options.timeoutMs;
    std::vector<verify::Outcome> outcomes = verify::verifyModule(*module, vo);
    for (Event &e : mlirErrors) a.errors.push_back(std::move(e));
    mlirErrors.clear();
    if (!a.errors.empty()) return fail(r, std::move(a.errors));

    std::map<std::string, std::vector<Event>> proofs;
    size_t bad = 0, unproved = 0;
    std::vector<Event> proofEvents;
    for (const verify::Outcome &o : outcomes) {
      Event e;
      e.kind = Event::Kind::Proof;
      e.name = o.function;
      e.text = o.claim;
      e.method = o.method;
      e.where = whereOf(a, o.where);
      for (const verify::ModelValue &v : o.counterexample)
        e.counterexample.emplace_back(v.name, v.value);
      switch (o.status) {
        case verify::Status::Proved: e.status = "proved"; break;
        case verify::Status::Failed: e.status = "failed"; ++bad; break;
        case verify::Status::Skipped:
          if (allowed(e)) {
            e.status = "allowed";
          } else {
            e.status = "unproved";
            ++unproved;
          }
          break;
      }
      proofs[o.function].push_back(e);
      if (mine.count(o.function) || (e.status != "proved" && e.status != "allowed"))
        proofEvents.push_back(std::move(e));
    }
    for (Event &e : proofEvents) {
      if (e.name.rfind(kEvalPrefix, 0) == 0) e.name.clear();
      r.events.push_back(std::move(e));
    }
    if (bad || unproved) {
      r.ok = false;
      std::string msg;
      if (bad) msg = plural(bad, "obligation") + " failed";
      if (unproved)
        msg += std::string(bad ? ", and " : "") + plural(unproved, "obligation") +
               " not proved (accept specific ones with :allow)";
      if (!replaced.empty())
        msg += "; the redefinition is not committed";
      else
        msg += "; nothing was committed";
      error(r.events, msg, Where{cellNo, 0, 0});
      return r;
    }
    if (mode == Mode::Check) {
      commit(base, items, proofs, newTypes);
      return r;
    }

    // Commit the definitions; the expressions are not kept.
    commit(base, items, proofs, newTypes);
    std::vector<std::pair<std::string, mlir::Type>> toRun;
    for (const Item &it : items) {
      if (it.entry.kind == "expression") continue;
      for (const std::string &n : it.entry.names) {
        if (!types.count(n)) continue;  // a type, metaprogram or operator
        Event e;
        bool redefined =
            std::find(replaced.begin(), replaced.end(), n) != replaced.end();
        e.kind = redefined ? Event::Kind::Redefined : Event::Kind::Defined;
        e.name = n;
        e.type = types[n];
        r.events.push_back(std::move(e));
        auto f = fns.find(n);
        if (f != fns.end() && f->second.getNumArguments() == 0 &&
            results[n] && showable(results[n]))
          toRun.emplace_back(n, results[n]);
      }
      if (it.entry.kind == "type" || it.entry.kind == "meta" ||
          it.entry.kind == "operator") {
        Event e;
        e.kind = Event::Kind::Defined;
        e.name = it.entry.head;
        e.type = it.entry.kind;
        r.events.push_back(std::move(e));
      }
    }
    for (auto &[name, t] : evals) {
      if (!showable(t)) {
        error(r.events, "values of type " + sema::typeName(t) +
                            " cannot be shown yet");
        r.ok = false;
        continue;
      }
      toRun.emplace_back(name, t);
    }
    if (!options.run || toRun.empty()) return r;
    run(*module, toRun, r, mlirErrors, a);
    return r;
  }

  // Compiles the verified module and runs each `(name, type)`.
  void run(mlir::ModuleOp module,
           const std::vector<std::pair<std::string, mlir::Type>> &toRun,
           CellResult &r, std::vector<Event> &mlirErrors, Attempt &a) {
    codegen::eraseContracts(module);
    if (mlir::failed(codegen::lowerToCore(module)) ||
        mlir::failed(codegen::lowerToLLVM(module))) {
      for (Event &e : mlirErrors) r.events.push_back(std::move(e));
      error(r.events, "this cannot be compiled yet, so it was not run");
      r.ok = false;
      return;
    }
    codegen::Options cg;
    cg.triple = llvm::sys::getProcessTriple();
    cg.cpu = llvm::sys::getHostCPUName().str();
    std::string jitError;
    mlir::ExecutionEngineOptions eo;
    auto builder = [&](mlir::Operation *op, llvm::LLVMContext &llvmCtx) {
      std::unique_ptr<llvm::Module> m = codegen::translate(
          mlir::cast<mlir::ModuleOp>(op), llvmCtx, cg, jitError);
      return m;
    };
    auto keep = [](llvm::Module *) { return llvm::Error::success(); };
    eo.llvmModuleBuilder = builder;
    eo.transformer = keep;
    eo.enableGDBNotificationListener = false;
    eo.enablePerfNotificationListener = false;
    llvm::Expected<std::unique_ptr<mlir::ExecutionEngine>> engine =
        mlir::ExecutionEngine::create(module, eo);
    if (!engine) {
      error(r.events, "JIT: " + (jitError.empty()
                                     ? llvm::toString(engine.takeError())
                                     : (llvm::consumeError(engine.takeError()),
                                        jitError)));
      r.ok = false;
      return;
    }
    (*engine)->initialize();
    for (const auto &[name, t] : toRun) {
      llvm::Expected<void *> fp = (*engine)->lookup(cName(name));
      if (!fp) {
        error(r.events, "JIT: " + llvm::toString(fp.takeError()));
        r.ok = false;
        continue;
      }
      std::string value = callAndFormat(*fp, t);
      if (name.rfind(kEvalPrefix, 0) == 0) {
        Event e;
        e.kind = Event::Kind::Value;
        e.type = t ? sema::typeName(t) : "unit";
        e.value = value;
        r.events.push_back(std::move(e));
      } else {
        for (Event &e : r.events)
          if ((e.kind == Event::Kind::Defined ||
               e.kind == Event::Kind::Redefined) &&
              e.name == name)
            e.value = value;
      }
    }
    (void)a;
  }

  template <typename Items>
  void commit(std::vector<Entry> base, const Items &items,
              std::map<std::string, std::vector<Event>> proofsNow,
              std::map<std::string, std::string> typesNow) {
    for (const auto &it : items)
      if (it.entry.kind != "expression") base.push_back(it.entry);
    env = std::move(base);
    proofs.clear();
    types.clear();
    for (auto &[name, list] : proofsNow)
      if (name.rfind(kEvalPrefix, 0) != 0) proofs[name] = std::move(list);
    for (auto &[name, t] : typesNow)
      if (name.rfind(kEvalPrefix, 0) != 0) types[name] = std::move(t);
  }

  // After a redefinition or :forget broke the build, says which
  // definitions still use the names that changed.
  void noteDependents(const Attempt &a, CellResult &r,
                      const std::vector<std::string> &changed) {
    if (changed.empty()) return;
    std::set<std::string> users;
    for (const NodePtr &k : a.tree->kids) {
      if (k->kind != NodeKind::LetItem) continue;
      std::set<std::string> refs;
      collectRefs(*k, refs);
      for (const std::string &c : changed)
        if (refs.count(c) && k->text != c) users.insert(k->text);
    }
    if (users.empty()) return;
    std::string list;
    for (const std::string &u : users) list += (list.empty() ? "'" : ", '") + u + "'";
    Event e;
    e.kind = Event::Kind::Info;
    e.text = "used by " + list;
    r.events.push_back(std::move(e));
  }

  CellResult fail(CellResult &r, std::vector<Event> errors) {
    for (Event &e : errors) r.events.push_back(std::move(e));
    r.ok = false;
    return r;
  }

  int ownerOf(const std::vector<Entry> &entries, const std::string &name) const {
    for (size_t i = 0; i < entries.size(); ++i)
      for (const std::string &n : entries[i].names)
        if (n == name) return static_cast<int>(i);
    return -1;
  }

  bool allowed(const Event &e) const {
    std::string w = formatWhere(e.where);
    for (const std::string &spec : options.allowUnproved) {
      if (spec.find(':') == std::string::npos) {
        if (spec == e.name) return true;
      } else if (w == spec || w.rfind(spec + ":", 0) == 0) {
        return true;
      }
    }
    return false;
  }

  // ---- commands ----------------------------------------------------------

  CellResult command(std::string_view text, unsigned cellNo) {
    CellResult r;
    r.cell = cellNo;
    std::string body = trim(text.substr(1));
    std::string word = body.substr(0, body.find_first_of(" \t\n"));
    std::string arg = trim(std::string_view(body).substr(word.size()));
    auto info = [&](std::string s) {
      Event e;
      e.kind = Event::Kind::Info;
      e.text = std::move(s);
      r.events.push_back(std::move(e));
    };
    auto needArg = [&]() {
      if (!arg.empty()) return true;
      error(r.events, ":" + word + " needs an argument; see :help");
      r.ok = false;
      return false;
    };

    if (word == "help" || word == "h" || word == "?") {
      info(helpText);
    } else if (word == "type" || word == "t") {
      if (!needArg()) return r;
      if (types.count(arg)) {
        Event e;
        e.kind = Event::Kind::Type;
        e.text = arg;
        e.type = types[arg];
        r.events.push_back(std::move(e));
        return r;
      }
      return code(arg, Mode::Type, cellNo);
    } else if (word == "proof" || word == "proofs") {
      if (arg.empty()) {
        for (const auto &[name, list] : proofs) {
          size_t proved = 0, allowedN = 0;
          for (const Event &e : list)
            (e.status == "proved" ? proved : allowedN) += 1;
          info(name + ": " + plural(proved, "obligation") + " proved" +
               (allowedN ? ", " + std::to_string(allowedN) + " allowed unproved"
                         : ""));
        }
        if (proofs.empty()) info("no obligations yet");
        return r;
      }
      auto it = proofs.find(arg);
      if (it == proofs.end()) {
        if (types.count(arg))
          info("'" + arg + "' has no obligations");
        else {
          error(r.events, "nothing named '" + arg + "' is defined");
          r.ok = false;
        }
        return r;
      }
      for (const Event &e : it->second) r.events.push_back(e);
    } else if (word == "env" || word == "list") {
      for (const Entry &e : env) {
        std::string what = e.kind == "expansion" ? "expanded" : e.kind;
        std::string line = "[" + std::to_string(e.cell) + "] " + what;
        for (const std::string &n : e.names)
          line += " " + n + (types.count(n) ? " : " + types[n] : "");
        if (e.names.empty()) line += " " + firstLine(e.source);
        info(line);
      }
      if (env.empty()) info("the environment is empty");
    } else if (word == "source" || word == "src") {
      if (!needArg()) return r;
      int i = ownerOf(env, arg);
      if (i < 0) {
        error(r.events, "nothing named '" + arg + "' is defined");
        r.ok = false;
      } else {
        info(env[i].source);
      }
    } else if (word == "redef") {
      if (!needArg()) return r;
      return code(arg, Mode::Redefine, cellNo);
    } else if (word == "forget") {
      if (!needArg()) return r;
      int i = ownerOf(env, arg);
      if (i < 0) {
        error(r.events, "nothing named '" + arg + "' is defined");
        r.ok = false;
        return r;
      }
      if (env[i].names.size() > 1) {
        error(r.events, "'" + arg + "' was defined together with other names; "
                        "use :redef to change that cell's code");
        r.ok = false;
        return r;
      }
      std::vector<Entry> saved = env;
      env.erase(env.begin() + i);
      CellResult c = code("", Mode::Check, cellNo, {arg});
      if (!c.ok) {
        env = std::move(saved);
        error(c.events, "cannot forget '" + arg + "'");
        return c;
      }
      Event e;
      e.kind = Event::Kind::Removed;
      e.name = arg;
      c.events.push_back(std::move(e));
      return c;
    } else if (word == "allow") {
      if (arg.empty()) {
        for (const std::string &s : options.allowUnproved) info(s);
        if (options.allowUnproved.empty())
          info("no unproved obligations are allowed");
        return r;
      }
      options.allowUnproved.push_back(arg);
      info("unproved obligations in " + arg + " are accepted from now on");
    } else if (word == "load") {
      if (!needArg()) return r;
      std::ifstream in(arg, std::ios::binary);
      if (!in) {
        error(r.events, "cannot open " + arg);
        r.ok = false;
        return r;
      }
      std::stringstream buf;
      buf << in.rdbuf();
      return code(buf.str(), Mode::Define, cellNo);
    } else if (word == "reset") {
      env.clear();
      proofs.clear();
      types.clear();
      info("the environment is empty");
    } else if (word == "quit" || word == "q") {
      info("bye");
    } else {
      error(r.events, "unknown command :" + word + "; see :help");
      r.ok = false;
    }
    return r;
  }

  static std::string firstLine(const std::string &s) {
    std::string l = s.substr(0, s.find('\n'));
    return l.size() > 60 ? l.substr(0, 57) + "..." : l;
  }
};

Session::Session(Options options)
    : impl_(std::make_unique<Impl>(std::move(options))) {}

Session::~Session() = default;

CellResult Session::execute(std::string_view cell) {
  unsigned n = ++impl_->cells;
  std::string t = trim(cell);
  if (!t.empty() && t[0] == ':') return impl_->command(t, n);
  return impl_->code(cell, Impl::Mode::Define, n);
}

void Session::reset() { impl_->command(":reset", ++impl_->cells); }

std::vector<std::string> Session::names() const {
  std::vector<std::string> out;
  for (const Entry &e : impl_->env)
    for (const std::string &n : e.names) out.push_back(n);
  return out;
}

bool Session::isComplete(std::string_view text) {
  std::string t = trim(text);
  if (t.empty() || t[0] == ':') return true;
  syntax::Diagnostics d;
  std::vector<syntax::Token> tokens = syntax::tokenize(text, d);
  for (const syntax::Diagnostic &e : d.errors())
    if (e.message.find("never closed") != std::string::npos ||
        e.message.find("unterminated") != std::string::npos)
      return false;
  if (d.hasErrors()) return true;  // let the parser report it
  const syntax::Token *last = nullptr;
  for (const syntax::Token &tok : tokens)
    if (tok.kind != syntax::TokenKind::Eof && tok.kind != syntax::TokenKind::Sep)
      last = &tok;
  if (!last) return true;
  using K = syntax::TokenKind;
  // A definition goes on until its `=`, so a header can be followed by
  // contracts on the lines after it.
  if (tokens[0].kind == K::Let) {
    int depth = 0;
    bool eq = false;
    for (const syntax::Token &tok : tokens) {
      switch (tok.kind) {
        case K::LParen: case K::LBracket: case K::LBrace: case K::LBraceAdj:
        case K::DotLBracket: case K::QuoteOpen: case K::SpliceOpen:
        case K::AttrOpen: case K::TargsOpen:
          ++depth;
          break;
        case K::RParen: case K::RBracket: case K::RBrace: case K::TargsClose:
          --depth;
          break;
        case K::Eq:
          if (depth == 0) eq = true;
          break;
        default:
          break;
      }
    }
    if (!eq) return false;
  }
  switch (last->kind) {
    case K::Eq: case K::Op: case K::Arrow: case K::FatArrow: case K::LArrow:
    case K::Bar: case K::Comma: case K::Colon: case K::Semi: case K::Let:
    case K::In: case K::If: case K::Then: case K::Else: case K::Do:
    case K::Requires: case K::Ensures: case K::Invariant: case K::Decreases:
    case K::Assert: case K::Assume: case K::Where: case K::Of: case K::With:
    case K::Match: case K::For: case K::While: case K::Spread: case K::Step:
    case K::Forall: case K::Exists: case K::Type: case K::Rec: case K::Meta:
    case K::Operator: case K::DotDot: case K::Dot:
      return false;
    default:
      return true;
  }
}

// ---- rendering ---------------------------------------------------------------

namespace {

const char *kindName(Event::Kind k) {
  switch (k) {
    case Event::Kind::Defined: return "defined";
    case Event::Kind::Redefined: return "redefined";
    case Event::Kind::Removed: return "removed";
    case Event::Kind::Value: return "value";
    case Event::Kind::Type: return "type";
    case Event::Kind::Proof: return "proof";
    case Event::Kind::Error: return "error";
    case Event::Kind::Info: return "info";
  }
  return "info";
}

std::string counterexample(const Event &e) {
  std::string out;
  for (const auto &[n, v] : e.counterexample)
    out += (out.empty() ? "" : ", ") + n + " = " + v;
  return out;
}

}  // namespace

std::string render(const CellResult &result) {
  std::map<std::string, size_t> proved;
  for (const Event &e : result.events)
    if (e.kind == Event::Kind::Proof && e.status == "proved") ++proved[e.name];
  std::ostringstream os;
  for (const Event &e : result.events) {
    std::string at = formatWhere(e.where);
    if (!at.empty()) at += ": ";
    switch (e.kind) {
      case Event::Kind::Defined:
      case Event::Kind::Redefined: {
        if (e.type == "type" || e.type == "meta" || e.type == "operator") {
          os << e.type << " " << e.name;
        } else {
          os << e.name << " : " << e.type;
          if (!e.value.empty()) os << " = " << e.value;
        }
        if (e.kind == Event::Kind::Redefined) os << "  (redefined)";
        if (proved[e.name])
          os << "  (* " << proved[e.name] << " proved *)";
        os << "\n";
        break;
      }
      case Event::Kind::Removed:
        os << "removed " << e.name << "\n";
        break;
      case Event::Kind::Value:
        os << "- : " << e.type << " = " << e.value << "\n";
        break;
      case Event::Kind::Type:
        os << e.text << " : " << e.type << "\n";
        break;
      case Event::Kind::Proof:
        if (e.status == "proved") {
          // Shown with the definition, unless the user asked for them.
          bool listing = true;
          for (const Event &x : result.events)
            if (x.kind != Event::Kind::Proof) listing = false;
          if (listing)
            os << at << "proved: " << e.text << " [" << e.method << "]\n";
          break;
        }
        os << at << e.status << ": " << e.text;
        if (!e.method.empty() && e.method != "counterexample")
          os << " [" << e.method << "]";
        if (!e.name.empty() && e.status != "failed") os << " in '" << e.name << "'";
        os << "\n";
        if (!e.counterexample.empty())
          os << "  counterexample: " << counterexample(e) << "\n";
        break;
      case Event::Kind::Error:
        os << at << "error: " << e.text << "\n";
        break;
      case Event::Kind::Info:
        os << e.text;
        if (e.text.empty() || e.text.back() != '\n') os << "\n";
        break;
    }
  }
  return os.str();
}

lsp::Json toJson(const Event &e) {
  lsp::Json j;
  j["kind"] = kindName(e.kind);
  if (!e.name.empty()) j["name"] = e.name;
  if (!e.type.empty()) j["type"] = e.type;
  if (!e.value.empty()) j["value"] = e.value;
  if (!e.text.empty()) j["text"] = e.text;
  if (!e.status.empty()) j["status"] = e.status;
  if (!e.method.empty()) j["method"] = e.method;
  if (!e.counterexample.empty()) {
    lsp::Json::Object ce;
    for (const auto &[n, v] : e.counterexample) ce[n] = v;
    j["counterexample"] = std::move(ce);
  }
  if (e.where.cell) {
    lsp::Json w;
    w["cell"] = e.where.cell;
    w["line"] = e.where.line;
    w["column"] = e.where.column;
    j["where"] = std::move(w);
  }
  return j;
}

lsp::Json toJson(const CellResult &r) {
  lsp::Json j;
  j["cell"] = r.cell;
  j["ok"] = r.ok;
  lsp::Json::Array events;
  for (const Event &e : r.events) events.push_back(toJson(e));
  j["events"] = std::move(events);
  return j;
}

}  // namespace pia::repl
