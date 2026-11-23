#include "repl/Session.h"

#include <algorithm>
#include <atomic>
#include <cctype>
#include <chrono>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <fstream>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <thread>

#include "codegen/Codegen.h"
#include "dialect/PiaDialect.h"
#include "irgen/IRGen.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/LLVMIR/LLVMDialect.h"
#include "mlir/ExecutionEngine/ExecutionEngine.h"
#include "mlir/IR/BuiltinTypes.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/MLIRContext.h"
#include "repl/State.h"
#include "sema/Sema.h"
#include "syntax/Lexer.h"
#include "syntax/Parser.h"
#include "verify/Verifier.h"
#include "llvm/ExecutionEngine/Orc/Core.h"
#include "llvm/ExecutionEngine/Orc/Mangling.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/Error.h"
#include "llvm/Support/TargetSelect.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/TargetParser/Host.h"

namespace pia::repl {

using syntax::Node;
using syntax::NodeKind;
using syntax::NodePtr;

namespace {

constexpr const char *kFile = "<repl>";
constexpr const char *kEvalPrefix = "__pia_eval_";
// The hidden function that proves a new body against an old contract.
constexpr const char *kRefinesPrefix = "__pia_refines_";
// Codegen's name for a function's internal version (codegen.md, "C ABI"),
// and the REPL's slot that holds a definition's current code.
constexpr const char *kInternalPrefix = "__pia_";
constexpr const char *kSlotPrefix = "__pia_slot_";
// The gate that counts the calls of a definition in progress, and the
// helpers every call goes through, so a swap can find a moment when none of
// a set of definitions is running (ADR 0031, "Live redefinition").
constexpr const char *kGatePrefix = "__pia_gate_";
constexpr const char *kWait = "__pia_repl_wait";

// A definition's gate. `active` counts its calls in progress on every
// thread. While `blocked` is set, a call waits unless it comes from a
// definition that is blocked too, so the blocked set drains.
struct Gate {
  std::atomic<int64_t> active{0};
  std::atomic<int32_t> blocked{0};
};
static_assert(sizeof(std::atomic<int64_t>) == 8 && alignof(Gate) == 8,
              "the gated call in callThroughSlots assumes this layout");

// The slow path of a gated call, taken only while `g` is blocked: the call
// has counted itself in `g` and found it blocked. `from` is the caller's
// gate, or null for a task's own expression.
extern "C" void piaReplWait(Gate *g, Gate *from) {
  for (;;) {
    if (!g->blocked.load(std::memory_order_seq_cst))
      return;
    if (from && from->blocked.load(std::memory_order_seq_cst))
      return;
    g->active.fetch_sub(1, std::memory_order_seq_cst);
    while (g->blocked.load(std::memory_order_seq_cst))
      std::this_thread::yield();
    g->active.fetch_add(1, std::memory_order_seq_cst);
  }
}

// A state's storage, as the JIT sees it, and the entry point that calls an
// expression with the states it takes (ADR 0031, "State").
constexpr const char *kStatePrefix = "__pia_state_";
constexpr const char *kThunkPrefix = "__pia_thunk_";

// Names the session makes up, which the environment never shows.
bool internalName(const std::string &n) {
  return n.rfind(kEvalPrefix, 0) == 0 || n.rfind(kRefinesPrefix, 0) == 0 ||
         n.rfind(kInitPrefix, 0) == 0;
}

std::string shadowing(const std::string &n, unsigned cell) {
  return "'" + n + "' is already defined in cell [" + std::to_string(cell) +
         "]; Pia does not allow shadowing (ADR 0022), so name it " + n +
         "' or replace it with :redef";
}

// Whether two function items take the same number and kinds of
// parameters. Their types are compared after lowering.
bool sameParams(const Node &a, const Node &b) {
  const Node &pa = *a.kids[0], &pb = *b.kids[0];
  if (pa.kids.size() != pb.kids.size())
    return false;
  for (size_t i = 0; i < pa.kids.size(); ++i)
    if (pa.kids[i]->kind != pb.kids[i]->kind)
      return false;
  return true;
}

// Renames the plain names in `n` by `map`, so an old contract can be read
// with the new definition's parameter names (a quote renames parameters).
void renameNames(Node &n, const std::map<std::string, std::string> &map) {
  if (n.kind == NodeKind::Name && n.flags.empty()) {
    auto it = map.find(n.text);
    if (it != map.end())
      n.text = it->second;
  }
  for (NodePtr &k : n.kids)
    renameNames(*k, map);
}

// The old definition's contract, with the new one's parameter names.
NodePtr contractFor(const Node &oldItem, const Node &newItem) {
  NodePtr c = syntax::clone(*oldItem.kids[2]);
  std::map<std::string, std::string> map;
  const Node &po = *oldItem.kids[0], &pn = *newItem.kids[0];
  for (size_t i = 0; i < po.kids.size() && i < pn.kids.size(); ++i)
    if (po.kids[i]->text != pn.kids[i]->text)
      map[po.kids[i]->text] = pn.kids[i]->text;
  if (!map.empty())
    renameNames(*c, map);
  return c;
}

template <typename OpTy, typename... Args>
OpTy build(mlir::OpBuilder &b, mlir::Location l, Args &&...args) {
#if LLVM_VERSION_MAJOR >= 21
  return OpTy::create(b, l, std::forward<Args>(args)...);
#else
  return b.create<OpTy>(l, std::forward<Args>(args)...);
#endif
}

// Makes every call of a definition in `defs` go through its slot: an
// external pointer the session owns and swaps when the definition changes
// (ADR 0031, "Live redefinition"). With `gated`, for code a task may run,
// each call also counts itself in the callee's gate before it loads the
// slot, and uncounts itself when it returns, so the gate counts the calls
// that may be running older code. The definitions' internal versions become
// visible, so the session can find their code.
mlir::LogicalResult callThroughSlots(mlir::ModuleOp m,
                                     const std::set<std::string> &defs,
                                     bool gated) {
  mlir::MLIRContext *ctx = m.getContext();
  mlir::OpBuilder b(ctx);
  auto ptr = mlir::LLVM::LLVMPointerType::get(ctx);
  size_t prefix = std::strlen(kInternalPrefix);
  auto voidTy = mlir::LLVM::LLVMVoidType::get(ctx);
  auto i64 = mlir::IntegerType::get(ctx, 64),
       i32 = mlir::IntegerType::get(ctx, 32);
  auto i8 = mlir::IntegerType::get(ctx, 8);
  auto waitTy = mlir::LLVM::LLVMFunctionType::get(voidTy, {ptr, ptr});
  auto global = [&](const std::string &name) {
    if (m.lookupSymbol(name))
      return;
    b.setInsertionPointToStart(m.getBody());
    build<mlir::LLVM::GlobalOp>(b, m.getLoc(), ptr, /*isConstant=*/false,
                                mlir::LLVM::Linkage::External, name,
                                mlir::Attribute());
  };
  mlir::LLVM::LLVMFuncOp wait;
  if (gated) {
    b.setInsertionPointToStart(m.getBody());
    wait = build<mlir::LLVM::LLVMFuncOp>(b, m.getLoc(), kWait, waitTy);
  }
  std::vector<mlir::LLVM::CallOp> calls;
  m.walk([&](mlir::LLVM::CallOp c) {
    std::optional<llvm::StringRef> callee = c.getCallee();
    if (callee && callee->starts_with(kInternalPrefix) &&
        defs.count(callee->drop_front(prefix).str()))
      calls.push_back(c);
  });
  for (mlir::LLVM::CallOp c : calls) {
    std::string def = c.getCallee()->drop_front(prefix).str();
    std::string slot = kSlotPrefix + def;
    global(slot);
    mlir::Location l = c.getLoc();
    mlir::Value g, one;
    if (gated) {
      // active += 1; if (blocked) wait (g, the caller's gate).
      std::string gate = kGatePrefix + def;
      global(gate);
      mlir::Value from;
      auto caller = c->getParentOfType<mlir::LLVM::LLVMFuncOp>();
      llvm::StringRef cn = caller.getName();
      b.setInsertionPoint(c);
      if (cn.starts_with(kInternalPrefix) &&
          defs.count(cn.drop_front(prefix).str())) {
        std::string fg = kGatePrefix + cn.drop_front(prefix).str();
        global(fg);
        b.setInsertionPoint(c);
        from = build<mlir::LLVM::AddressOfOp>(b, l, ptr, fg);
      } else {
        from = build<mlir::LLVM::ZeroOp>(b, l, ptr);
      }
      g = build<mlir::LLVM::AddressOfOp>(b, l, ptr, gate);
      one = build<mlir::LLVM::ConstantOp>(b, l, i64, b.getI64IntegerAttr(1));
      build<mlir::LLVM::AtomicRMWOp>(b, l, mlir::LLVM::AtomicBinOp::add, g, one,
                                     mlir::LLVM::AtomicOrdering::seq_cst);
      auto bp = build<mlir::LLVM::GEPOp>(b, l, ptr, i8, g,
                                         llvm::ArrayRef<mlir::LLVM::GEPArg>{8});
      auto blocked = build<mlir::LLVM::LoadOp>(b, l, i32, bp, /*alignment=*/4);
      blocked.setOrdering(mlir::LLVM::AtomicOrdering::seq_cst);
      auto zero =
          build<mlir::LLVM::ConstantOp>(b, l, i32, b.getI32IntegerAttr(0));
      auto isBlocked = build<mlir::LLVM::ICmpOp>(
          b, l, mlir::LLVM::ICmpPredicate::ne, blocked, zero);
      mlir::Block *before = c->getBlock();
      mlir::Block *cont = before->splitBlock(c);
      mlir::Block *slow = b.createBlock(cont);
      b.setInsertionPointToEnd(slow);
      build<mlir::LLVM::CallOp>(b, l, wait, mlir::ValueRange{g, from});
      build<mlir::LLVM::BrOp>(b, l, mlir::ValueRange{}, cont);
      b.setInsertionPointToEnd(before);
      build<mlir::LLVM::CondBrOp>(b, l, isBlocked, slow, cont);
    }
    b.setInsertionPoint(c);
    auto addr = build<mlir::LLVM::AddressOfOp>(b, c.getLoc(), ptr, slot);
    auto fp =
        build<mlir::LLVM::LoadOp>(b, c.getLoc(), ptr, addr, /*alignment=*/8);
    fp.setOrdering(mlir::LLVM::AtomicOrdering::acquire);
    llvm::SmallVector<mlir::Value> operands{fp};
    operands.append(c.getArgOperands().begin(), c.getArgOperands().end());
    auto call = build<mlir::LLVM::CallOp>(b, c.getLoc(),
                                          c.getCalleeFunctionType(), operands);
    c.replaceAllUsesWith(call.getResults());
    c.erase();
    if (gated) {
      b.setInsertionPointAfter(call);
      build<mlir::LLVM::AtomicRMWOp>(b, l, mlir::LLVM::AtomicBinOp::sub, g, one,
                                     mlir::LLVM::AtomicOrdering::seq_cst);
    }
  }
  for (const std::string &def : defs)
    if (auto f =
            m.lookupSymbol<mlir::LLVM::LLVMFuncOp>(kInternalPrefix + def)) {
      f.setLinkage(mlir::LLVM::Linkage::External);
    }
  return mlir::success();
}

std::string trim(std::string_view s) {
  size_t b = 0, e = s.size();
  while (b < e && std::isspace(static_cast<unsigned char>(s[b])))
    ++b;
  while (e > b && std::isspace(static_cast<unsigned char>(s[e - 1])))
    --e;
  return std::string(s.substr(b, e - b));
}

std::string trimRight(std::string_view s) {
  size_t e = s.size();
  while (e > 0 && std::isspace(static_cast<unsigned char>(s[e - 1])))
    --e;
  return std::string(s.substr(0, e));
}

unsigned countLines(std::string_view s) {
  unsigned n = 0;
  for (char c : s)
    n += c == '\n';
  return n;
}

// "'a'", "'a' and 'b'", "'a', 'b' and 'c'".
std::string joinNames(const std::vector<std::string> &names, const char *last) {
  std::string out;
  for (size_t i = 0; i < names.size(); ++i) {
    if (i)
      out += i + 1 == names.size() ? std::string(" ") + last + " " : ", ";
    out += "'" + names[i] + "'";
  }
  return out;
}

std::string plural(size_t n, const char *word) {
  return std::to_string(n) + " " + word + (n == 1 ? "" : "s");
}

// "[3]:2:5", the way locations inside cells are written.
std::string formatWhere(const Where &w) {
  if (w.cell == 0)
    return "";
  std::string out = "[" + std::to_string(w.cell) + "]";
  if (w.line)
    out += ":" + std::to_string(w.line);
  if (w.column)
    out += ":" + std::to_string(w.column);
  return out;
}

// The C name of a function's entry point (docs/codegen.md, "C ABI").
std::string cName(const std::string &name) {
  std::string out;
  for (char c : name)
    out += c == '\'' ? std::string("_prime") : std::string(1, c);
  return out;
}

// One definition in the environment: the text of a top-level item, kept as
// the user wrote it so the environment can be parsed again with each cell.
struct Entry {
  unsigned cell = 0;
  unsigned line = 1;  // the item's first line within its cell
  std::string source; // the item, without trailing whitespace
  std::string kind;   // "let", "type", "meta", "operator", "expansion"
  std::string head;   // the name it was written with, if any
  std::vector<std::string> names; // what it defines, after expansion
};

// Where a stretch of the combined source came from.
struct Segment {
  uint32_t offset = 0, end = 0; // byte range in the combined source
  unsigned vline = 1;           // its first line there
  unsigned cell = 0, line = 1;  // and in its cell
  int entry = -1;               // index into the env, or -1 for the cell
};

// A function's type as Pia writes it: `(a : u8) -> (b : u8) -> u8`, or the
// result type alone for a constant.
// The states a function takes are left out: they are not its arguments.
std::string functionType(mlir::func::FuncOp fn,
                         const std::set<std::string> &states = {},
                         bool unit = false) {
  mlir::FunctionType t = fn.getFunctionType();
  std::string out = unit ? "() -> " : "";
  for (unsigned i = 0; i < t.getNumInputs(); ++i) {
    std::string name;
    // A theory's abstract function has no body, so no arguments to name.
    if (!fn.isExternal())
      if (auto nl = mlir::dyn_cast<mlir::NameLoc>(fn.getArgument(i).getLoc()))
        name = nl.getName().str();
    name = name.substr(0, name.find('#')); // a quote's renamed parameter
    if (states.count(name))
      continue;
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

// A function's type without its parameter names, for comparing two
// versions of a definition. Types are written in full, so a record whose
// fields changed gives a different shape.
std::string functionShape(mlir::func::FuncOp fn) {
  std::string out;
  llvm::raw_string_ostream os(out);
  fn.getFunctionType().print(os);
  return os.str();
}

// The C layout of a record result: each field at its natural offset.
struct Layout {
  size_t size = 0, align = 1;
};

std::optional<Layout> layoutOf(mlir::Type t) {
  if (t.isInteger(1))
    return Layout{1, 1};
  if (auto it = mlir::dyn_cast<IntType>(t)) {
    size_t bytes = it.getStorageWidth() / 8;
    return Layout{bytes, bytes};
  }
  if (auto r = mlir::dyn_cast<RecordType>(t)) {
    Layout l;
    for (mlir::Type f : r.getFieldTypes()) {
      std::optional<Layout> fl = layoutOf(f);
      if (!fl)
        return std::nullopt;
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
  std::memcpy(&u, p, bytes); // little endian, like every target Pia has
  if (!isSigned)
    return std::to_string(u);
  unsigned bits = bytes * 8;
  int64_t s = bits == 64
                  ? static_cast<int64_t>(u)
                  : static_cast<int64_t>(u << (64 - bits)) >> (64 - bits);
  return std::to_string(s);
}

// Formats the value of type `t` stored at `p` in C layout.
std::string formatValue(mlir::Type t, const unsigned char *p) {
  if (t.isInteger(1))
    return *p ? "true" : "false";
  if (auto it = mlir::dyn_cast<IntType>(t))
    return formatInt(it, p);
  auto r = mlir::cast<RecordType>(t);
  std::string out = "{ ";
  size_t offset = 0;
  for (size_t i = 0; i < r.getFieldTypes().size(); ++i) {
    mlir::Type f = r.getFieldTypes()[i];
    Layout fl = *layoutOf(f);
    offset = (offset + fl.align - 1) / fl.align * fl.align;
    if (i)
      out += "; ";
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
  if (t.isInteger(1))
    return reinterpret_cast<bool (*)()>(fp)() ? "true" : "false";
  if (auto it = mlir::dyn_cast<IntType>(t)) {
    unsigned char buf[8] = {0};
    bool s = it.getLo().isNegative();
    auto store = [&](auto v) { std::memcpy(buf, &v, sizeof v); };
    switch (it.getStorageWidth()) {
    case 8:
      s ? store(reinterpret_cast<int8_t (*)()>(fp)())
        : store(reinterpret_cast<uint8_t (*)()>(fp)());
      break;
    case 16:
      s ? store(reinterpret_cast<int16_t (*)()>(fp)())
        : store(reinterpret_cast<uint16_t (*)()>(fp)());
      break;
    case 32:
      s ? store(reinterpret_cast<int32_t (*)()>(fp)())
        : store(reinterpret_cast<uint32_t (*)()>(fp)());
      break;
    default:
      s ? store(reinterpret_cast<int64_t (*)()>(fp)())
        : store(reinterpret_cast<uint64_t (*)()>(fp)());
      break;
    }
    return formatInt(it, buf);
  }
  // A record comes back through a pointer to a C struct of its fields.
  Layout l = *layoutOf(t);
  std::vector<uint64_t> storage(l.size / 8 + 1, 0);
  reinterpret_cast<void (*)(void *)>(fp)(storage.data());
  return formatValue(t,
                     reinterpret_cast<const unsigned char *>(storage.data()));
}

bool showable(mlir::Type t) { return !t || layoutOf(t).has_value(); }

// Calls a JIT-compiled entry point that takes nothing and returns an integer
// or a bool, and stores the result at `out` in C layout.
void callInto(void *fp, mlir::Type t, unsigned char *out) {
  auto store = [&](auto v) { std::memcpy(out, &v, sizeof v); };
  if (t.isInteger(1)) {
    store(reinterpret_cast<bool (*)()>(fp)());
    return;
  }
  auto it = mlir::cast<IntType>(t);
  bool s = it.getLo().isNegative();
  switch (it.getStorageWidth()) {
  case 8:
    s ? store(reinterpret_cast<int8_t (*)()>(fp)())
      : store(reinterpret_cast<uint8_t (*)()>(fp)());
    break;
  case 16:
    s ? store(reinterpret_cast<int16_t (*)()>(fp)())
      : store(reinterpret_cast<uint16_t (*)()>(fp)());
    break;
  case 32:
    s ? store(reinterpret_cast<int32_t (*)()>(fp)())
      : store(reinterpret_cast<uint32_t (*)()>(fp)());
    break;
  default:
    s ? store(reinterpret_cast<int64_t (*)()>(fp)())
      : store(reinterpret_cast<uint64_t (*)()>(fp)());
    break;
  }
}

// Adds `__pia_thunk_<e>` for each expression `e` that takes states: it calls
// `e`'s entry point with the states' storage, which the session registers as
// `__pia_state_<name>`, so the thunk has the signature of an expression
// that takes nothing.
mlir::LogicalResult
addThunks(mlir::ModuleOp m,
          const std::map<std::string, std::vector<std::string>> &evals) {
  mlir::MLIRContext *ctx = m.getContext();
  mlir::OpBuilder b(ctx);
  auto ptr = mlir::LLVM::LLVMPointerType::get(ctx);
  for (const auto &[eval, states] : evals) {
    auto entry = m.lookupSymbol<mlir::LLVM::LLVMFuncOp>(cName(eval));
    if (!entry)
      continue;
    mlir::LLVM::LLVMFunctionType ty = entry.getFunctionType();
    if (ty.getNumParams() < states.size())
      return mlir::failure();
    for (size_t i = 0; i < states.size(); ++i)
      if (!mlir::isa<mlir::LLVM::LLVMPointerType>(ty.getParamType(i)))
        return mlir::failure();
    for (const std::string &st : states)
      if (!m.lookupSymbol(kStatePrefix + st)) {
        b.setInsertionPointToStart(m.getBody());
        build<mlir::LLVM::GlobalOp>(b, m.getLoc(), b.getI64Type(),
                                    /*isConstant=*/false,
                                    mlir::LLVM::Linkage::External,
                                    kStatePrefix + st, mlir::Attribute());
      }
    llvm::SmallVector<mlir::Type> rest(ty.getParams().begin() + states.size(),
                                       ty.getParams().end());
    auto thunkTy = mlir::LLVM::LLVMFunctionType::get(ty.getReturnType(), rest);
    b.setInsertionPointToEnd(m.getBody());
    auto thunk = build<mlir::LLVM::LLVMFuncOp>(b, m.getLoc(),
                                               kThunkPrefix + eval, thunkTy);
    mlir::Block *blk = thunk.addEntryBlock(b);
    b.setInsertionPointToStart(blk);
    llvm::SmallVector<mlir::Value> args;
    for (const std::string &st : states)
      args.push_back(build<mlir::LLVM::AddressOfOp>(b, m.getLoc(), ptr,
                                                    kStatePrefix + st));
    for (mlir::BlockArgument a : blk->getArguments())
      args.push_back(a);
    auto call = build<mlir::LLVM::CallOp>(b, m.getLoc(), entry, args);
    if (mlir::isa<mlir::LLVM::LLVMVoidType>(ty.getReturnType()))
      build<mlir::LLVM::ReturnOp>(b, m.getLoc(), mlir::ValueRange{});
    else
      build<mlir::LLVM::ReturnOp>(b, m.getLoc(), call.getResults());
  }
  return mlir::success();
}

// The names of the top-level functions that `n` refers to.
void collectRefs(const Node &n, std::set<std::string> &out) {
  if (n.kind == NodeKind::Name)
    out.insert(n.text);
  for (const NodePtr &k : n.kids)
    collectRefs(*k, out);
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
    "  :spawn <expr>     run an expression as a background task\n"
    "  :tasks            list the tasks and their values\n"
    "  :wait <n>         wait for task n to finish\n"
    "  :load <file>      run a file as one cell\n"
    "  :reset            empty the environment\n"
    "  :help             this list\n"
    "  :quit             leave\n"
    "A definition joins the environment only if everything still verifies.\n"
    "`let x : mutable T invariant p = v` is a state: it keeps its value, "
    "every\n"
    "definition keeps p, and `:redef` of it can migrate `old x`.\n"
    "While a task runs, a definition it can reach is swapped into it live: at\n"
    "once if the new body is proved against the old contract, or else "
    "together\n"
    "with its callers, at a moment when no task is running any of them.\n";

} // namespace

struct Session::Impl {
  Options options;
  mlir::MLIRContext ctx;
  std::vector<Entry> env;
  unsigned cells = 0;
  // The obligations of each function, from the last cell that committed.
  std::map<std::string, std::vector<Event>> proofs;
  std::map<std::string, std::string> types;  // name -> type, as shown
  std::map<std::string, std::string> shapes; // name -> type, unnamed
  // What each definition refers to, for the reach of running tasks.
  std::map<std::string, std::set<std::string>> refs;

  // Live code (ADR 0031): each definition is called through its slot, which
  // points at its newest code. Engines stay alive while a task runs code in
  // them.
  std::map<std::string, std::unique_ptr<std::atomic<void *>>> slots;
  std::map<std::string, std::unique_ptr<Gate>> gates;
  std::vector<std::shared_ptr<mlir::ExecutionEngine>> engines;
  struct Task;
  std::vector<std::unique_ptr<Task>> tasks;
  unsigned taskCount = 0;
  std::string pendingSpawn;               // the expression :spawn runs
  std::set<std::string> pendingSpawnRefs; // and what it refers to

  // State (ADR 0031, "State"): each state's storage, which compiled code
  // reaches as `__pia_state_<name>`, and the states each definition takes.
  struct StateSlot {
    std::unique_ptr<uint64_t> cell = std::make_unique<uint64_t>(0);
    mlir::Type type;
  };
  std::map<std::string, StateSlot> stateSlots;
  std::map<std::string, std::vector<std::string>> stateUses;
  // The expressions of the cell being compiled that take states.
  std::map<std::string, std::vector<std::string>> pendingThunks;
  std::set<std::string> pendingSpawnStates;
  std::vector<std::unique_ptr<uint64_t>> retiredStates;

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

  ~Impl() {
    // A task still running keeps its engine: the process is ending, and
    // its code must not be freed under it.
    for (auto &t : tasks) {
      if (t->done.load(std::memory_order_acquire)) {
        if (t->thread.joinable())
          t->thread.join();
      } else {
        t->thread.detach();
        new std::shared_ptr<mlir::ExecutionEngine>(t->engine);
      }
    }
  }

  // ---- one attempt at the environment plus a cell ----------------------

  enum class Mode { Define, Redefine, Type, Check, Spawn };

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
    if (c == std::string::npos || c == 0)
      return Where{};
    size_t l = loc.rfind(':', c - 1);
    if (l == std::string::npos)
      return Where{};
    unsigned line = std::strtoul(loc.c_str() + l + 1, nullptr, 10);
    unsigned col = std::strtoul(loc.c_str() + c + 1, nullptr, 10);
    return where(a, line, col);
  }

  const Segment *segmentAt(const Attempt &a, uint32_t offset) const {
    for (const Segment &s : a.segments)
      if (offset >= s.offset && offset < s.end)
        return &s;
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

  // Joins `entries` and `cell` into one program and parses it. With `wrap`,
  // the cell is read as one parenthesised expression, on lines of its own so
  // that locations inside it stay the same.
  Attempt parse(const std::vector<Entry> &entries, std::string_view cell,
                unsigned cellNo, bool wrap = false) {
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
    if (wrap) {
      s.line = 0;
      a.source += "(\n";
    }
    a.source += cell;
    a.source += wrap ? "\n)\n" : "\n";
    s.end = a.source.size();
    a.segments.push_back(s);

    syntax::Diagnostics d;
    a.tree = syntax::parseProgram(a.source, d);
    takeDiagnostics(a, d);
    return a;
  }

  // ---- cells -------------------------------------------------------------

  struct Item {
    Entry entry;
    NodeKind kind;
    uint32_t offset;
  };

  // A cell's code. `forgotten` names what :forget is taking out.
  CellResult code(std::string_view text, Mode mode, unsigned cellNo,
                  std::vector<std::string> forgotten = {}) {
    CellResult r;
    r.cell = cellNo;
    std::vector<Entry> base = env;
    std::set<int> doomed; // entries a redefinition replaces

    Attempt a = parse(base, text, cellNo);
    // A statement such as `count <- 7` is not a top-level item, but a cell
    // can be one: read it as an expression.
    if (!a.errors.empty() && trim(text).rfind("let", 0) != 0) {
      Attempt w = parse(base, text, cellNo, true);
      if (w.errors.empty())
        a = std::move(w);
    }
    if (!a.errors.empty())
      return fail(r, std::move(a.errors));

    std::vector<Item> items;
    for (size_t i = 0; i < a.tree->kids.size(); ++i) {
      const Node &k = *a.tree->kids[i];
      if (k.loc.offset < a.cellOffset)
        continue;
      uint32_t end = i + 1 < a.tree->kids.size()
                         ? a.tree->kids[i + 1]->loc.offset
                         : static_cast<uint32_t>(a.source.size());
      Item it;
      it.kind = k.kind;
      it.offset = k.loc.offset;
      it.entry.cell = cellNo;
      it.entry.line = where(a, k.loc.line, k.loc.column).line;
      it.entry.source = trimRight(
          std::string_view(a.source).substr(k.loc.offset, end - k.loc.offset));
      if (k.kind == NodeKind::LetItem) {
        it.entry.head = k.text;
        it.entry.kind = k.flags.find("meta") != std::string::npos ? "meta"
                        : sema::isTypeItem(k)                     ? "type"
                        : isStateItem(k)                          ? "state"
                                                                  : "let";
      } else if (k.kind == NodeKind::MetaOperator) {
        it.entry.head = "(" + k.text + ")";
        it.entry.kind = "operator";
      } else if (k.kind == NodeKind::ExprItem) {
        it.entry.kind = "expansion"; // until we know it is an expression
      } else {
        it.entry.kind = "item";
      }
      items.push_back(std::move(it));
    }
    if (items.empty() && mode != Mode::Check && mode != Mode::Type)
      return r; // only comments
    if (mode == Mode::Spawn &&
        (items.size() != 1 || items[0].kind != NodeKind::ExprItem)) {
      error(r.events, ":spawn needs one expression");
      r.ok = false;
      return r;
    }

    // What the cell's own definitions replace.
    for (const Item &it : items) {
      if (it.entry.head.empty())
        continue;
      int owner = ownerOf(base, it.entry.head, doomed);
      if (owner < 0) {
        if (mode == Mode::Redefine) {
          error(r.events, "there is no '" + it.entry.head + "' to redefine",
                Where{cellNo, it.entry.line, 1});
          r.ok = false;
        }
        continue;
      }
      if (mode != Mode::Redefine) {
        error(r.events, shadowing(it.entry.head, base[owner].cell),
              Where{cellNo, it.entry.line, 1});
        r.ok = false;
      } else if (base[owner].kind == "expansion") {
        error(r.events,
              "'" + it.entry.head +
                  "' was generated by a metaprogram in cell [" +
                  std::to_string(base[owner].cell) + "]; redefine that instead",
              Where{cellNo, it.entry.line, 1});
        r.ok = false;
      } else {
        doomed.insert(owner);
      }
    }
    if (!r.ok)
      return r;

    // Run the metaprograms, with the definitions being replaced still in
    // place, so the old and new versions can be compared.
    syntax::Diagnostics d;
    meta::Options mo = options.meta;
    mo.live = true;
    meta::expand(*a.tree, d, mo);
    takeDiagnostics(a, d);
    if (!a.errors.empty())
      return fail(r, std::move(a.errors));

    // `redefine` (Pia.Live) marks generated definitions as replacements.
    for (const NodePtr &k : a.tree->kids) {
      if (k->kind != NodeKind::LetItem)
        continue;
      size_t at = k->flags.find("redef");
      if (at == std::string::npos)
        continue;
      k->flags.erase(at, 5);
      while (!k->flags.empty() && k->flags.back() == ' ')
        k->flags.pop_back();
      while (!k->flags.empty() && k->flags.front() == ' ')
        k->flags.erase(0, 1);
      for (const NodePtr &o : a.tree->kids) {
        if (o.get() == k.get() || o->kind != NodeKind::LetItem ||
            o->text != k->text)
          continue;
        const Segment *s = segmentAt(a, o->loc.offset);
        if (!s || s->entry < 0 || doomed.count(s->entry))
          continue;
        if (base[s->entry].kind != "let" && base[s->entry].kind != "type" &&
            base[s->entry].kind != "meta") {
          error(r.events,
                "'" + k->text + "' was generated by a metaprogram in cell [" +
                    std::to_string(base[s->entry].cell) +
                    "], so 'redefine' cannot replace it",
                where(a, k->loc.line, k->loc.column));
          r.ok = false;
          continue;
        }
        doomed.insert(s->entry);
      }
    }
    if (!r.ok)
      return r;

    // Take the replaced definitions out, keeping a copy of each.
    std::vector<std::string> replaced;
    std::map<std::string, NodePtr> oldItems;
    for (int i : doomed)
      for (const std::string &n : base[i].names)
        replaced.push_back(n);
    for (auto it = a.tree->kids.begin(); it != a.tree->kids.end();) {
      const Segment *s = segmentAt(a, (*it)->loc.offset);
      if (s && s->entry >= 0 && doomed.count(s->entry) &&
          (*it)->kind != NodeKind::ExprItem) {
        if ((*it)->kind == NodeKind::LetItem)
          oldItems[(*it)->text] = std::move(*it);
        it = a.tree->kids.erase(it);
      } else {
        ++it;
      }
    }

    std::map<int, std::vector<std::string>> envNames; // entry -> names
    std::vector<std::string> cellNames;
    std::set<uint32_t> exprOffsets;
    std::vector<std::pair<std::string, mlir::Type>> evals;
    unsigned evalCount = 0;
    for (Item &it : items)
      if (!it.entry.head.empty())
        it.entry.names = {it.entry.head};
    // The cell item a generated definition came from: the last one that
    // starts at or before its location (the expansion site).
    auto cellItemAt = [&](uint32_t offset) -> Item * {
      Item *best = nullptr;
      for (Item &it : items)
        if (it.offset <= offset)
          best = &it;
      return best;
    };
    std::map<std::string, const Node *> newItems;
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
      if (k->kind != NodeKind::LetItem || !s)
        continue;
      if (s->entry >= 0) {
        envNames[s->entry].push_back(k->text);
        if (oldItems.count(k->text))
          newItems[k->text] = k.get();
        continue;
      }
      cellNames.push_back(k->text);
      newItems[k->text] = k.get();
      if (Item *it = cellItemAt(k->loc.offset))
        if (std::find(it->entry.names.begin(), it->entry.names.end(),
                      k->text) == it->entry.names.end())
          it->entry.names.push_back(k->text);
    }
    for (Item &it : items)
      if (it.kind == NodeKind::ExprItem && exprOffsets.count(it.offset))
        it.entry.kind = "expression";
    // What each older definition defines now: a metaprogram it calls may
    // generate different names than it did.
    for (size_t i = 0; i < base.size(); ++i) {
      if (doomed.count(static_cast<int>(i)))
        continue;
      std::vector<std::string> names;
      if (!base[i].head.empty())
        names.push_back(base[i].head);
      for (const std::string &n : envNames[static_cast<int>(i)])
        if (std::find(names.begin(), names.end(), n) == names.end())
          names.push_back(n);
      base[i].names = std::move(names);
    }
    for (const Item &it : items)
      for (const std::string &n : it.entry.names) {
        if (n == it.entry.head)
          continue; // checked above
        int owner = ownerOf(base, n, doomed);
        if (owner < 0)
          continue;
        if (oldItems.count(n))
          continue; // a `redefine`
        error(r.events, shadowing(n, base[owner].cell),
              Where{cellNo, it.entry.line, 1});
        r.ok = false;
      }
    if (!r.ok)
      return r;

    // State: every definition that uses one takes it as a buffer.
    std::vector<Node *> oldList;
    for (auto &[n, item] : oldItems)
      oldList.push_back(item.get());
    std::vector<std::pair<syntax::SourceLoc, std::string>> stateErrors;
    StateUse su = rewriteState(
        *a.tree, oldList,
        [&](const Node &k) {
          const Segment *seg = segmentAt(a, k.loc.offset);
          return !seg || seg->entry < 0;
        },
        stateErrors);
    for (auto &[loc, msg] : stateErrors)
      error(a.errors, msg, where(a, loc.line, loc.column));
    if (!a.errors.empty())
      return fail(r, std::move(a.errors));
    std::set<std::string> stateNames;
    for (const StateDecl &d : su.states) {
      stateNames.insert(d.name);
      newItems.erase(d.name); // replaced by its initial value's function
    }
    std::set<std::string> cellStates; // the states this cell defines
    for (const std::string &n : cellNames)
      if (stateNames.count(n))
        cellStates.insert(n);
    // A state a running task uses is the task's alone: nothing else may
    // read, write, replace or remove it while the task runs.
    {
      std::set<std::string> touched(cellStates.begin(), cellStates.end());
      for (auto &[name, t] : evals) {
        auto u = su.uses.find(name);
        if (u != su.uses.end())
          touched.insert(u->second.begin(), u->second.end());
      }
      for (const std::string &n : forgotten)
        touched.insert(n);
      for (const std::string &n : replaced)
        touched.insert(n);
      for (const std::string &st : touched) {
        std::string owners = tasksUsingState(st);
        if (owners.empty())
          continue;
        error(r.events,
              "the state '" + st + "' belongs to a running task (" + owners +
                  ") until it finishes; wait for it with :wait",
              Where{cellNo, 0, 0});
        r.ok = false;
      }
      if (!r.ok)
        return r;
    }
    pendingThunks.clear();
    for (auto &[name, t] : evals) {
      auto u = su.uses.find(name);
      if (u != su.uses.end())
        pendingThunks[name] = u->second;
    }
    // The states whose new value comes from the old one.
    std::set<std::string> migrating;
    for (const StateDecl &d : su.states)
      if (d.migrates) {
        migrating.insert(d.name);
        pendingThunks[kInitPrefix + d.name] = {d.name};
      }

    // While tasks run, a replaced definition they can reach must refine the
    // one they were proved against (ADR 0031): its new body is proved
    // against the old contract, as a hidden function.
    std::set<std::string> live = reachedByTasks();
    std::map<std::string, std::string> users; // name -> "task 1, 2"
    for (const std::string &n : live)
      users[n] = tasksReaching(n);
    std::vector<std::string> mustRefine;
    for (const std::string &n : replaced)
      if (live.count(n))
        mustRefine.push_back(n);
    for (const std::string &n : forgotten)
      if (live.count(n)) {
        error(r.events, "'" + n + "' is in use by a running task (" +
                            tasksReaching(n) + "); wait for it with :wait");
        r.ok = false;
      }
    if (!r.ok)
      return r;
    // Why a definition a task can reach does not refine its old version.
    // Each such change is swapped together with its callers, at a moment
    // when no task is running any of them.
    std::map<std::string, std::string> refinesWhy;
    for (const std::string &n : mustRefine) {
      auto o = oldItems.find(n);
      auto nw = newItems.find(n);
      if (o == oldItems.end() || nw == newItems.end() ||
          sema::isTypeItem(*o->second) || sema::isTypeItem(*nw->second)) {
        error(r.events,
              "'" + n + "' is in use by a running task (" + users[n] +
                  "), and a generated definition cannot change while running "
                  "code uses it; wait for the task with :wait",
              Where{cellNo, 0, 0});
        r.ok = false;
        continue;
      }
      if (!sameParams(*o->second, *nw->second)) {
        refinesWhy[n] = "its parameters changed";
        continue;
      }
      NodePtr check = syntax::clone(*nw->second);
      check->text = kRefinesPrefix + n;
      check->kids[2] = contractFor(*o->second, *nw->second);
      a.tree->add(std::move(check));
    }
    if (!r.ok)
      return r;

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
    for (Event &e : mlirErrors)
      a.errors.push_back(std::move(e));
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
    std::map<std::string, std::string> newShapes;
    std::set<std::string> nullary; // compiling replaces the func ops
    for (auto &[name, f] : fns) {
      if (f.getFunctionType().getNumInputs() == 0)
        nullary.insert(name);
      newTypes[name] = functionType(f, stateNames, su.unitFns.count(name) > 0);
      newShapes[name] = functionShape(f);
      mlir::FunctionType t = f.getFunctionType();
      results[name] = t.getNumResults() ? t.getResult(0) : mlir::Type();
    }
    for (auto &[name, t] : evals)
      t = results[name];
    for (const StateDecl &d : su.states) {
      if (!cellStates.count(d.name))
        continue;
      mlir::Type t = results[kInitPrefix + d.name];
      if (!t || !(t.isInteger(1) || mlir::isa<IntType>(t))) {
        error(r.events,
              "the state '" + d.name +
                  "' must be an integer or a bool, for now",
              where(a, d.loc.line, d.loc.column));
        r.ok = false;
      }
    }
    if (!r.ok)
      return r;
    // A type that changed changes the shapes of the functions that use it,
    // whether or not they were redefined.
    for (const std::string &n : live)
      if (!refinesWhy.count(n) && shapes.count(n) && newShapes.count(n) &&
          newShapes[n] != shapes[n])
        refinesWhy[n] =
            "its type changed from " + types[n] + " to " + newTypes[n];

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
    for (auto &[name, t] : evals)
      mine.insert(name);
    verify::Options vo;
    vo.timeoutMs = options.timeoutMs;
    std::vector<verify::Outcome> outcomes = verify::verifyModule(*module, vo);
    for (Event &e : mlirErrors)
      a.errors.push_back(std::move(e));
    mlirErrors.clear();
    if (!a.errors.empty())
      return fail(r, std::move(a.errors));

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
      bool refinement = o.function.rfind(kRefinesPrefix, 0) == 0;
      if (o.function.rfind(kInitPrefix, 0) == 0)
        e.name = o.function.substr(std::strlen(kInitPrefix));
      switch (o.status) {
      case verify::Status::Proved:
        e.status = "proved";
        break;
      case verify::Status::Failed:
        e.status = "failed";
        break;
      case verify::Status::Skipped:
        e.status = allowed(e) ? "allowed" : "unproved";
        break;
      }
      if (refinement) {
        std::string n = o.function.substr(std::strlen(kRefinesPrefix));
        if ((e.status == "failed" || e.status == "unproved") &&
            !refinesWhy.count(n))
          refinesWhy[n] =
              "the new body does not meet the old contract: " + e.text +
              " (the old contract at " + formatWhere(e.where) + ")";
        continue;
      }
      bad += e.status == "failed";
      unproved += e.status == "unproved";
      proofs[e.name].push_back(e);
      if (mine.count(e.name) || (e.status != "proved" && e.status != "allowed"))
        proofEvents.push_back(std::move(e));
    }
    for (Event &e : proofEvents) {
      if (e.name.rfind(kEvalPrefix, 0) == 0)
        e.name.clear();
      r.events.push_back(std::move(e));
    }
    if (bad || unproved) {
      r.ok = false;
      std::string msg;
      if (bad)
        msg = plural(bad, "obligation") + " failed";
      if (unproved)
        msg += std::string(bad ? ", and " : "") +
               plural(unproved, "obligation") +
               " not proved (accept specific ones with :allow)";
      if (!replaced.empty())
        msg += "; the redefinition is not committed";
      else
        msg += "; nothing was committed";
      error(r.events, msg, Where{cellNo, 0, 0});
      return r;
    }
    // The definitions to swap together: those that do not refine their old
    // versions, and every definition that calls one of them, in its old
    // version or its new one. Their callers outside the set rely only on
    // contracts that did not change.
    std::map<std::string, std::set<std::string>> newRefs;
    for (const NodePtr &k : a.tree->kids)
      if (k->kind == NodeKind::LetItem && !internalName(k->text))
        collectRefs(*k, newRefs[k->text]);
    std::set<std::string> quiet;
    for (const auto &[n, why] : refinesWhy)
      quiet.insert(n);
    for (const std::string &m : live)
      for (const auto &[n, why] : refinesWhy) {
        if (m == n)
          continue;
        auto calls =
            [&](const std::map<std::string, std::set<std::string>> &rs) {
              auto it = rs.find(m);
              return it != rs.end() && it->second.count(n);
            };
        if (calls(refs) || calls(newRefs))
          quiet.insert(m);
      }

    std::set<std::string> defs;
    for (const auto &[name, t] : newTypes)
      if (!internalName(name))
        defs.insert(name);
    std::shared_ptr<mlir::ExecutionEngine> engine;
    if (!quiet.empty()) {
      engine =
          options.run ? compile(*module, defs, r, mlirErrors, true) : nullptr;
      std::vector<std::string> busy;
      if (!engine || !install(engine, defs, quiet, busy)) {
        std::vector<std::string> changed, callers;
        std::string why;
        for (const auto &[n, w] : refinesWhy) {
          changed.push_back(n);
          why += (why.empty() ? "" : "; ") +
                 (refinesWhy.size() > 1 ? n + ": " : std::string()) + w;
        }
        for (const std::string &q : quiet)
          if (!refinesWhy.count(q))
            callers.push_back(q);
        std::set<std::string> ts;
        for (const std::string &q : quiet)
          ts.insert(users[q]);
        std::string tasksList;
        for (const std::string &t : ts)
          tasksList += (tasksList.empty() ? "" : ", ") + t;
        std::string msg = joinNames(changed, "and") +
                          " no longer refines what running code was proved "
                          "against (" +
                          why + "), so it can only be swapped";
        if (!callers.empty())
          msg += " together with " + joinNames(callers, "and") + ", which " +
                 (callers.size() > 1 ? "call" : "calls") + " it,";
        msg += " at a moment when no task is running any of them";
        if (!engine)
          msg += ", and the new code cannot be compiled";
        else
          msg += ", but " + tasksList + " stayed inside " +
                 (busy.empty() ? std::string("them") : joinNames(busy, "and")) +
                 " for " + std::to_string(options.quiesceMs) + " ms";
        msg += "; nothing was committed (wait for the task with :wait)";
        error(r.events, msg, Where{cellNo, 0, 0});
        r.ok = false;
        return r;
      }
    }

    // Commit the definitions; the expressions are not kept.
    std::vector<Entry> kept;
    for (size_t i = 0; i < base.size(); ++i)
      if (!doomed.count(static_cast<int>(i)))
        kept.push_back(base[i]);
    // A state that keeps its value keeps the proofs of its initial value.
    for (const std::string &st : stateNames)
      if (!cellStates.count(st) && this->proofs.count(st))
        proofs[st] = this->proofs[st];
    commit(kept, items, proofs, newTypes, *a.tree);
    shapes.clear();
    for (auto &[name, sh] : newShapes)
      if (!internalName(name))
        shapes[name] = sh;
    stateUses.clear();
    for (auto &[name, u] : su.uses)
      if (!internalName(name))
        stateUses[name] = u;
    for (auto it = stateSlots.begin(); it != stateSlots.end();)
      if (!stateNames.count(it->first)) {
        // Code may still name the old cell, so it is kept, not freed.
        retiredStates.push_back(std::move(it->second.cell));
        it = stateSlots.erase(it);
      } else {
        ++it;
      }
    std::map<std::string, mlir::Type> oldStateTypes;
    for (const std::string &st : cellStates) {
      auto was = stateSlots.find(st);
      if (was != stateSlots.end() && was->second.type)
        oldStateTypes[st] = was->second.type;
      stateSlots[st].type = results[kInitPrefix + st];
    }
    pendingSpawnStates.clear();
    for (auto &[name, u] : pendingThunks)
      if (name.rfind(kEvalPrefix, 0) == 0)
        pendingSpawnStates.insert(u.begin(), u.end());

    std::string quietList =
        joinNames(std::vector<std::string>(quiet.begin(), quiet.end()), "or");
    auto swapText = [&](const std::string &n) {
      std::string t = "swapped into running " + users[n];
      if (quiet.count(n))
        t += " at a moment when no task was running " + quietList;
      return t;
    };
    auto finish =
        [&](const std::vector<std::pair<std::string, mlir::Type>> &toRun,
            bool spawn) {
          if (!engine) {
            // Code a task may run counts its calls, so a later swap can wait
            // for the task to leave what it changes.
            engine = compile(*module, defs, r, mlirErrors,
                             spawn || anyTaskRunning());
            std::vector<std::string> busy;
            if (!engine)
              return;
            install(engine, defs, {}, busy);
          }
          // A state this cell defines starts at its initial value.
          for (const std::string &st : cellStates) {
            llvm::Expected<void *> fp = engine->lookup(
                migrating.count(st)
                    ? kThunkPrefix + std::string(kInitPrefix) + st
                    : cName(kInitPrefix + st));
            if (!fp) {
              error(r.events, "JIT: " + llvm::toString(fp.takeError()));
              r.ok = false;
              continue;
            }
            StateSlot &slot = stateSlots[st];
            uint64_t v = 0; // a migration reads the old value from the cell
            callInto(*fp, slot.type, reinterpret_cast<unsigned char *>(&v));
            *slot.cell = v;
            for (Event &e : r.events)
              if ((e.kind == Event::Kind::Defined ||
                   e.kind == Event::Kind::Redefined) &&
                  e.name == st)
                e.value = formatValue(
                    slot.type,
                    reinterpret_cast<const unsigned char *>(slot.cell.get()));
          }
          execute(engine, toRun, r, spawn);
        };
    if (mode == Mode::Check) {
      if (options.run && anyTaskRunning() && (!forgotten.empty() || engine))
        finish({}, false);
      return r;
    }
    std::vector<std::pair<std::string, mlir::Type>> toRun;
    for (const Item &it : items) {
      if (it.entry.kind == "expression")
        continue;
      for (const std::string &n : it.entry.names) {
        if (!types.count(n))
          continue; // a type, metaprogram or operator
        Event e;
        bool redefined =
            std::find(replaced.begin(), replaced.end(), n) != replaced.end();
        e.kind = redefined ? Event::Kind::Redefined : Event::Kind::Defined;
        e.name = n;
        e.type = types[n];
        if (redefined && live.count(n))
          e.text = swapText(n);
        r.events.push_back(std::move(e));
        if (nullary.count(n) && results[n] && showable(results[n]))
          toRun.emplace_back(n, results[n]);
      }
      if (it.entry.kind == "state") {
        Event e;
        e.kind = std::find(replaced.begin(), replaced.end(), it.entry.head) !=
                         replaced.end()
                     ? Event::Kind::Redefined
                     : Event::Kind::Defined;
        e.name = it.entry.head;
        e.type = "mutable " + sema::typeName(stateSlots[it.entry.head].type);
        auto was = oldStateTypes.find(it.entry.head);
        if (migrating.count(it.entry.head) && was != oldStateTypes.end())
          e.text = "migrated from mutable " + sema::typeName(was->second);
        r.events.push_back(std::move(e));
      }
      if (it.entry.kind == "type" || it.entry.kind == "meta" ||
          it.entry.kind == "operator") {
        Event e;
        e.kind = std::find(replaced.begin(), replaced.end(), it.entry.head) !=
                         replaced.end()
                     ? Event::Kind::Redefined
                     : Event::Kind::Defined;
        e.name = it.entry.head;
        e.type = it.entry.kind;
        if (e.kind == Event::Kind::Redefined && !quiet.empty())
          e.text = "swapped into running " + users[*quiet.begin()] +
                   " at a moment when no task was running " + quietList;
        r.events.push_back(std::move(e));
      }
    }
    // Definitions a `redefine` replaced in an older cell's expansion.
    for (const std::string &n : replaced) {
      bool shown = false;
      for (const Event &e : r.events)
        if (e.name == n && (e.kind == Event::Kind::Redefined))
          shown = true;
      if (shown || !types.count(n))
        continue;
      Event e;
      e.kind = Event::Kind::Redefined;
      e.name = n;
      e.type = types[n];
      if (live.count(n))
        e.text = swapText(n);
      r.events.push_back(std::move(e));
    }
    for (auto &[name, t] : evals) {
      if (!showable(t)) {
        error(r.events,
              "values of type " + sema::typeName(t) + " cannot be shown yet");
        r.ok = false;
        continue;
      }
      toRun.emplace_back(name, t);
    }
    bool swap = !replaced.empty() && !live.empty();
    if (!options.run ||
        (toRun.empty() && !swap && !engine && cellStates.empty()))
      return r;
    finish(toRun, mode == Mode::Spawn);
    return r;
  }

  // ---- compiling and running ---------------------------------------------

  // Compiles the verified module into a new JIT engine whose calls between
  // `defs` go through their slots and gates. Null if it cannot be compiled.
  std::shared_ptr<mlir::ExecutionEngine>
  compile(mlir::ModuleOp module, const std::set<std::string> &defs,
          CellResult &r, std::vector<Event> &mlirErrors, bool gated) {
    codegen::eraseContracts(module);
    if (mlir::failed(codegen::lowerToCore(module)) ||
        mlir::failed(codegen::lowerToLLVM(module)) ||
        mlir::failed(callThroughSlots(module, defs, gated)) ||
        mlir::failed(addThunks(module, pendingThunks))) {
      for (Event &e : mlirErrors)
        r.events.push_back(std::move(e));
      error(r.events, "this cannot be compiled yet, so it was not run");
      r.ok = false;
      return nullptr;
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
    llvm::Expected<std::unique_ptr<mlir::ExecutionEngine>> created =
        mlir::ExecutionEngine::create(module, eo);
    if (!created) {
      error(r.events, "JIT: " + (jitError.empty()
                                     ? llvm::toString(created.takeError())
                                     : (llvm::consumeError(created.takeError()),
                                        jitError)));
      r.ok = false;
      return nullptr;
    }
    std::shared_ptr<mlir::ExecutionEngine> engine = std::move(*created);
    for (const std::string &n : defs) {
      if (!slots.count(n))
        slots[n] = std::make_unique<std::atomic<void *>>(nullptr);
      if (!gates.count(n))
        gates[n] = std::make_unique<Gate>();
    }
    engine->registerSymbols([&](llvm::orc::MangleAndInterner interner) {
      llvm::orc::SymbolMap map;
      auto add = [&](const std::string &name, void *p) {
        map[interner(name)] = {llvm::orc::ExecutorAddr::fromPtr(p),
                               llvm::JITSymbolFlags::Exported};
      };
      for (const auto &[n, slot] : slots)
        add(kSlotPrefix + n, slot.get());
      for (const auto &[n, gate] : gates)
        add(kGatePrefix + n, gate.get());
      for (const auto &[n, st] : stateSlots)
        add(kStatePrefix + n, st.cell.get());
      add(kWait, reinterpret_cast<void *>(&piaReplWait));
      return map;
    });
    engine->initialize();
    return engine;
  }

  // Points every definition's slot at the engine's code. Calls that start
  // from now on run it; calls already running finish on the code they
  // started in. With a `quiet` set, the slots change only at a moment when
  // no call of any of them is in progress: calls into the set from outside
  // it wait while it drains, for at most `quiesceMs`. On a timeout nothing
  // changes, and `busy` names the definitions that were still running.
  bool install(const std::shared_ptr<mlir::ExecutionEngine> &engine,
               const std::set<std::string> &defs,
               const std::set<std::string> &quiet,
               std::vector<std::string> &busy) {
    std::map<std::string, void *> code;
    for (const std::string &n : defs) {
      llvm::Expected<void *> fp = engine->lookup(kInternalPrefix + n);
      if (!fp) {
        llvm::consumeError(fp.takeError());
        continue; // folded away, or not a function
      }
      code[n] = *fp;
    }
    std::vector<Gate *> held;
    for (const std::string &n : quiet)
      if (gates.count(n))
        held.push_back(gates[n].get());
    for (Gate *g : held)
      g->blocked.store(1, std::memory_order_seq_cst);
    auto deadline = std::chrono::steady_clock::now() +
                    std::chrono::milliseconds(options.quiesceMs);
    std::set<std::string> neverIdle(quiet.begin(), quiet.end());
    for (;;) {
      bool idle = true;
      for (const std::string &n : quiet) {
        auto g = gates.find(n);
        if (g == gates.end())
          continue;
        if (g->second->active.load(std::memory_order_seq_cst) != 0)
          idle = false;
        else
          neverIdle.erase(n);
      }
      if (idle)
        break;
      if (std::chrono::steady_clock::now() >= deadline) {
        // The definitions a task never left: the ones keeping the set busy.
        busy.assign(neverIdle.begin(), neverIdle.end());
        for (Gate *g : held)
          g->blocked.store(0, std::memory_order_seq_cst);
        return false;
      }
      std::this_thread::yield();
    }
    for (const auto &[n, fp] : code)
      slots[n]->store(fp, std::memory_order_release);
    for (Gate *g : held)
      g->blocked.store(0, std::memory_order_seq_cst);
    reapEngines();
    engines.push_back(engine);
    return true;
  }

  // Runs each `(name, type)` in the engine, or starts it as a task.
  void execute(const std::shared_ptr<mlir::ExecutionEngine> &engine,
               const std::vector<std::pair<std::string, mlir::Type>> &toRun,
               CellResult &r, bool spawn) {
    for (const auto &[name, t] : toRun) {
      llvm::Expected<void *> fp = engine->lookup(
          pendingThunks.count(name) ? kThunkPrefix + name : cName(name));
      if (!fp) {
        error(r.events, "JIT: " + llvm::toString(fp.takeError()));
        r.ok = false;
        continue;
      }
      if (spawn && name.rfind(kEvalPrefix, 0) == 0) {
        startTask(*fp, t, engine, r);
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
  }

  // ---- tasks ---------------------------------------------------------------

  struct Task {
    unsigned id = 0;
    unsigned cell = 0;
    std::string expr;
    std::string type;
    std::set<std::string> reach;  // definitions its code can call
    std::set<std::string> states; // the states it uses, which are its alone
    std::shared_ptr<mlir::ExecutionEngine> engine;
    std::thread thread;
    std::atomic<bool> done{false};
    std::string value; // set before done
  };

  void startTask(void *fp, mlir::Type t,
                 std::shared_ptr<mlir::ExecutionEngine> engine, CellResult &r) {
    auto task = std::make_unique<Task>();
    task->id = ++taskCount;
    task->cell = r.cell;
    task->expr = pendingSpawn;
    task->type = t ? sema::typeName(t) : "unit";
    task->reach = reachOf(pendingSpawnRefs);
    task->states = pendingSpawnStates;
    for (const std::string &n : task->reach) {
      auto u = stateUses.find(n);
      if (u != stateUses.end())
        task->states.insert(u->second.begin(), u->second.end());
    }
    task->engine = std::move(engine);
    Task *raw = task.get();
    task->thread = std::thread([raw, fp, t] {
      raw->value = callAndFormat(fp, t);
      raw->done.store(true, std::memory_order_release);
    });
    r.events.push_back(taskEvent(*raw));
    tasks.push_back(std::move(task));
  }

  Event taskEvent(const Task &t) const {
    Event e;
    e.kind = Event::Kind::Task;
    e.name = std::to_string(t.id);
    e.text = t.expr;
    e.type = t.type;
    bool done = t.done.load(std::memory_order_acquire);
    e.status = done ? "done" : "running";
    if (done)
      e.value = t.value;
    e.where = Where{t.cell, 0, 0};
    return e;
  }

  bool anyTaskRunning() const {
    for (const auto &t : tasks)
      if (!t->done.load(std::memory_order_acquire))
        return true;
    return false;
  }

  // The definitions that running tasks can reach.
  std::set<std::string> reachedByTasks() const {
    std::set<std::string> out;
    for (const auto &t : tasks)
      if (!t->done.load(std::memory_order_acquire))
        out.insert(t->reach.begin(), t->reach.end());
    return out;
  }

  std::string tasksUsingState(const std::string &st) const {
    std::string out;
    for (const auto &t : tasks)
      if (!t->done.load(std::memory_order_acquire) && t->states.count(st))
        out += (out.empty() ? "task " : ", ") + std::to_string(t->id);
    return out;
  }

  std::string tasksReaching(const std::string &n) const {
    std::string out;
    for (const auto &t : tasks)
      if (!t->done.load(std::memory_order_acquire) && t->reach.count(n))
        out += (out.empty() ? "task " : ", ") + std::to_string(t->id);
    return out;
  }

  // Everything `roots` can call, through the environment's definitions.
  std::set<std::string> reachOf(const std::set<std::string> &roots) const {
    std::set<std::string> out;
    std::vector<std::string> work(roots.begin(), roots.end());
    while (!work.empty()) {
      std::string n = work.back();
      work.pop_back();
      if (!types.count(n) || !out.insert(n).second)
        continue;
      auto it = refs.find(n);
      if (it != refs.end())
        for (const std::string &m : it->second)
          work.push_back(m);
    }
    return out;
  }

  // Frees the engines no running task uses. The newest one stays, since
  // the slots point into it.
  void reapEngines() {
    std::set<mlir::ExecutionEngine *> used;
    for (const auto &t : tasks)
      if (!t->done.load(std::memory_order_acquire))
        used.insert(t->engine.get());
    for (auto &t : tasks)
      if (t->done.load(std::memory_order_acquire) && t->thread.joinable())
        t->thread.join();
    for (auto &t : tasks)
      if (t->done.load(std::memory_order_acquire))
        t->engine.reset();
    std::vector<std::shared_ptr<mlir::ExecutionEngine>> keep;
    for (auto &e : engines)
      if (used.count(e.get()))
        keep.push_back(e);
    engines = std::move(keep);
  }

  template <typename Items>
  void commit(std::vector<Entry> base, const Items &items,
              std::map<std::string, std::vector<Event>> proofsNow,
              std::map<std::string, std::string> typesNow, const Node &tree) {
    for (const auto &it : items)
      if (it.entry.kind != "expression")
        base.push_back(it.entry);
    env = std::move(base);
    proofs.clear();
    types.clear();
    for (auto &[name, list] : proofsNow)
      if (internalName(name))
        continue;
      else
        proofs[name] = std::move(list);
    for (auto &[name, t] : typesNow)
      if (internalName(name))
        continue;
      else
        types[name] = std::move(t);
    refs.clear();
    for (const NodePtr &k : tree.kids) {
      if (k->kind != NodeKind::LetItem)
        continue;
      std::set<std::string> rs;
      collectRefs(*k, rs);
      if (k->text.rfind(kEvalPrefix, 0) == 0) {
        pendingSpawnRefs = rs;
        continue;
      }
      refs[k->text] = std::move(rs);
    }
    // Running tasks can now reach what the new definitions call.
    for (auto &t : tasks)
      if (!t->done.load(std::memory_order_acquire)) {
        std::set<std::string> more = reachOf(t->reach);
        t->reach.insert(more.begin(), more.end());
      }
  }

  // After a redefinition or :forget broke the build, says which
  // definitions still use the names that changed.
  void noteDependents(const Attempt &a, CellResult &r,
                      const std::vector<std::string> &changed) {
    if (changed.empty())
      return;
    std::set<std::string> users;
    for (const NodePtr &k : a.tree->kids) {
      if (k->kind != NodeKind::LetItem)
        continue;
      std::set<std::string> refs;
      collectRefs(*k, refs);
      for (const std::string &c : changed)
        if (refs.count(c) && k->text != c)
          users.insert(k->text);
    }
    if (users.empty())
      return;
    std::string list;
    for (const std::string &u : users)
      list += (list.empty() ? "'" : ", '") + u + "'";
    Event e;
    e.kind = Event::Kind::Info;
    e.text = "used by " + list;
    r.events.push_back(std::move(e));
  }

  CellResult fail(CellResult &r, std::vector<Event> errors) {
    for (Event &e : errors)
      r.events.push_back(std::move(e));
    r.ok = false;
    return r;
  }

  int ownerOf(const std::vector<Entry> &entries, const std::string &name,
              const std::set<int> &skip = {}) const {
    for (size_t i = 0; i < entries.size(); ++i) {
      if (skip.count(static_cast<int>(i)))
        continue;
      for (const std::string &n : entries[i].names)
        if (n == name)
          return static_cast<int>(i);
    }
    return -1;
  }

  bool allowed(const Event &e) const {
    std::string w = formatWhere(e.where);
    for (const std::string &spec : options.allowUnproved) {
      if (spec.find(':') == std::string::npos) {
        if (spec == e.name)
          return true;
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
      if (!arg.empty())
        return true;
      error(r.events, ":" + word + " needs an argument; see :help");
      r.ok = false;
      return false;
    };

    if (word == "help" || word == "h" || word == "?") {
      info(helpText);
    } else if (word == "type" || word == "t") {
      if (!needArg())
        return r;
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
        if (proofs.empty())
          info("no obligations yet");
        return r;
      }
      auto it = proofs.find(arg);
      if (it == proofs.end()) {
        if (types.count(arg) || stateSlots.count(arg))
          info("'" + arg + "' has no obligations");
        else {
          error(r.events, "nothing named '" + arg + "' is defined");
          r.ok = false;
        }
        return r;
      }
      for (const Event &e : it->second)
        r.events.push_back(e);
    } else if (word == "env" || word == "list") {
      for (const Entry &e : env) {
        std::string what = e.kind == "expansion" ? "expanded" : e.kind;
        std::string line = "[" + std::to_string(e.cell) + "] " + what;
        for (const std::string &n : e.names)
          line += " " + n + (types.count(n) ? " : " + types[n] : "");
        if (e.names.empty())
          line += " " + firstLine(e.source);
        info(line);
      }
      if (env.empty())
        info("the environment is empty");
    } else if (word == "source" || word == "src") {
      if (!needArg())
        return r;
      int i = ownerOf(env, arg);
      if (i < 0) {
        error(r.events, "nothing named '" + arg + "' is defined");
        r.ok = false;
      } else {
        info(env[i].source);
      }
    } else if (word == "redef") {
      if (!needArg())
        return r;
      return code(arg, Mode::Redefine, cellNo);
    } else if (word == "forget") {
      if (!needArg())
        return r;
      int i = ownerOf(env, arg);
      if (i < 0) {
        error(r.events, "nothing named '" + arg + "' is defined");
        r.ok = false;
        return r;
      }
      if (env[i].names.size() > 1) {
        error(r.events, "'" + arg +
                            "' was defined together with other names; "
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
        for (const std::string &s : options.allowUnproved)
          info(s);
        if (options.allowUnproved.empty())
          info("no unproved obligations are allowed");
        return r;
      }
      options.allowUnproved.push_back(arg);
      info("unproved obligations in " + arg + " are accepted from now on");
    } else if (word == "load") {
      if (!needArg())
        return r;
      std::ifstream in(arg, std::ios::binary);
      if (!in) {
        error(r.events, "cannot open " + arg);
        r.ok = false;
        return r;
      }
      std::stringstream buf;
      buf << in.rdbuf();
      // A literate file's code is its ```pia blocks (ADR 0029). Blanking the
      // prose keeps locations those of the Markdown.
      if (syntax::isLiterateFileName(arg))
        return code(syntax::literateCode(buf.str()), Mode::Define, cellNo);
      return code(buf.str(), Mode::Define, cellNo);
    } else if (word == "spawn") {
      if (!needArg())
        return r;
      pendingSpawn = arg;
      return code(arg, Mode::Spawn, cellNo);
    } else if (word == "tasks") {
      for (const auto &t : tasks)
        r.events.push_back(taskEvent(*t));
      if (tasks.empty())
        info("no tasks");
    } else if (word == "wait") {
      if (!needArg())
        return r;
      unsigned id = std::strtoul(arg.c_str(), nullptr, 10);
      Task *task = nullptr;
      for (auto &t : tasks)
        if (t->id == id)
          task = t.get();
      if (!task) {
        error(r.events, "there is no task " + arg);
        r.ok = false;
        return r;
      }
      if (task->thread.joinable())
        task->thread.join();
      r.events.push_back(taskEvent(*task));
      reapEngines();
    } else if (word == "reset") {
      if (anyTaskRunning()) {
        error(r.events, "tasks are still running; wait for them with :wait");
        r.ok = false;
        return r;
      }
      env.clear();
      refs.clear();
      shapes.clear();
      stateUses.clear();
      for (auto &[n, st] : stateSlots)
        retiredStates.push_back(std::move(st.cell));
      stateSlots.clear();
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
  if (!t.empty() && t[0] == ':')
    return impl_->command(t, n);
  return impl_->code(cell, Impl::Mode::Define, n);
}

void Session::reset() { impl_->command(":reset", ++impl_->cells); }

std::vector<std::string> Session::names() const {
  std::vector<std::string> out;
  for (const Entry &e : impl_->env)
    for (const std::string &n : e.names)
      out.push_back(n);
  return out;
}

bool Session::isComplete(std::string_view text) {
  std::string t = trim(text);
  if (t.empty() || t[0] == ':')
    return true;
  // A definition's contracts come before its `=`, so a last line that is a
  // contract clause needs the body still to come.
  size_t nl = t.rfind('\n');
  std::string lastLine = trim(t.substr(nl == std::string::npos ? 0 : nl + 1));
  for (const char *clause : {"requires", "ensures", "decreases", "invariant"}) {
    size_t n = std::strlen(clause);
    if (lastLine.compare(0, n, clause) == 0 &&
        (lastLine.size() == n ||
         !std::isalnum(static_cast<unsigned char>(lastLine[n]))))
      return false;
  }
  syntax::Diagnostics d;
  std::vector<syntax::Token> tokens = syntax::tokenize(text, d);
  for (const syntax::Diagnostic &e : d.errors())
    if (e.message.find("never closed") != std::string::npos ||
        e.message.find("unterminated") != std::string::npos)
      return false;
  if (d.hasErrors())
    return true; // let the parser report it
  const syntax::Token *last = nullptr;
  for (const syntax::Token &tok : tokens)
    if (tok.kind != syntax::TokenKind::Eof &&
        tok.kind != syntax::TokenKind::Sep)
      last = &tok;
  if (!last)
    return true;
  using K = syntax::TokenKind;
  // A definition goes on until its `=`, so a header can be followed by
  // contracts on the lines after it.
  if (tokens[0].kind == K::Let) {
    int depth = 0;
    bool eq = false;
    for (const syntax::Token &tok : tokens) {
      switch (tok.kind) {
      case K::LParen:
      case K::LBracket:
      case K::LBrace:
      case K::LBraceAdj:
      case K::DotLBracket:
      case K::QuoteOpen:
      case K::SpliceOpen:
      case K::AttrOpen:
      case K::TargsOpen:
        ++depth;
        break;
      case K::RParen:
      case K::RBracket:
      case K::RBrace:
      case K::TargsClose:
        --depth;
        break;
      case K::Eq:
        if (depth == 0)
          eq = true;
        break;
      default:
        break;
      }
    }
    if (!eq)
      return false;
  }
  switch (last->kind) {
  case K::Eq:
  case K::Op:
  case K::Arrow:
  case K::FatArrow:
  case K::LArrow:
  case K::Bar:
  case K::Comma:
  case K::Colon:
  case K::Semi:
  case K::Let:
  case K::In:
  case K::If:
  case K::Then:
  case K::Else:
  case K::Do:
  case K::Requires:
  case K::Ensures:
  case K::Invariant:
  case K::Decreases:
  case K::Assert:
  case K::Assume:
  case K::Where:
  case K::Of:
  case K::With:
  case K::Match:
  case K::For:
  case K::While:
  case K::Spread:
  case K::Step:
  case K::Forall:
  case K::Exists:
  case K::Type:
  case K::Rec:
  case K::Meta:
  case K::Operator:
  case K::DotDot:
  case K::Dot:
    return false;
  default:
    return true;
  }
}

// ---- rendering
// ---------------------------------------------------------------

namespace {

const char *kindName(Event::Kind k) {
  switch (k) {
  case Event::Kind::Defined:
    return "defined";
  case Event::Kind::Redefined:
    return "redefined";
  case Event::Kind::Removed:
    return "removed";
  case Event::Kind::Value:
    return "value";
  case Event::Kind::Type:
    return "type";
  case Event::Kind::Proof:
    return "proof";
  case Event::Kind::Error:
    return "error";
  case Event::Kind::Info:
    return "info";
  case Event::Kind::Task:
    return "task";
  }
  return "info";
}

std::string counterexample(const Event &e) {
  std::string out;
  for (const auto &[n, v] : e.counterexample)
    out += (out.empty() ? "" : ", ") + n + " = " + v;
  return out;
}

} // namespace

std::string render(const CellResult &result) {
  std::map<std::string, size_t> proved;
  for (const Event &e : result.events)
    if (e.kind == Event::Kind::Proof && e.status == "proved")
      ++proved[e.name];
  std::ostringstream os;
  for (const Event &e : result.events) {
    std::string at = formatWhere(e.where);
    if (!at.empty())
      at += ": ";
    switch (e.kind) {
    case Event::Kind::Defined:
    case Event::Kind::Redefined: {
      if (e.type == "type" || e.type == "meta" || e.type == "operator") {
        os << e.type << " " << e.name;
      } else {
        os << e.name << " : " << e.type;
        if (!e.value.empty())
          os << " = " << e.value;
      }
      if (e.kind == Event::Kind::Redefined)
        os << "  (redefined" << (e.text.empty() ? "" : ", " + e.text) << ")";
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
          if (x.kind != Event::Kind::Proof)
            listing = false;
        if (listing)
          os << at << "proved: " << e.text << " [" << e.method << "]\n";
        break;
      }
      os << at << e.status << ": " << e.text;
      if (!e.method.empty() && e.method != "counterexample")
        os << " [" << e.method << "]";
      if (!e.name.empty() && e.status != "failed")
        os << " in '" << e.name << "'";
      os << "\n";
      if (!e.counterexample.empty())
        os << "  counterexample: " << counterexample(e) << "\n";
      break;
    case Event::Kind::Error:
      os << at << "error: " << e.text << "\n";
      break;
    case Event::Kind::Task:
      os << "task " << e.name << " (" << e.text << ") ";
      if (e.status == "done")
        os << "done: " << e.type << " = " << e.value << "\n";
      else
        os << "running\n";
      break;
    case Event::Kind::Info:
      os << e.text;
      if (e.text.empty() || e.text.back() != '\n')
        os << "\n";
      break;
    }
  }
  return os.str();
}

lsp::Json toJson(const Event &e) {
  lsp::Json j;
  j["kind"] = kindName(e.kind);
  if (!e.name.empty())
    j["name"] = e.name;
  if (!e.type.empty())
    j["type"] = e.type;
  if (!e.value.empty())
    j["value"] = e.value;
  if (!e.text.empty())
    j["text"] = e.text;
  if (!e.status.empty())
    j["status"] = e.status;
  if (!e.method.empty())
    j["method"] = e.method;
  if (!e.counterexample.empty()) {
    lsp::Json::Object ce;
    for (const auto &[n, v] : e.counterexample)
      ce[n] = v;
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
  for (const Event &e : r.events)
    events.push_back(toJson(e));
  j["events"] = std::move(events);
  return j;
}

} // namespace pia::repl
