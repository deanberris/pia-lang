#include "codegen/Lowerings.h"
#include "codegen/Codegen.h"

#include <array>
#include <cctype>
#include <map>
#include <set>
#include <string>

#include "mlir/Conversion/AffineToStandard/AffineToStandard.h"
#include "mlir/Dialect/Affine/IR/AffineOps.h"
#include "mlir/Dialect/Arith/IR/Arith.h"
#include "mlir/Dialect/Bufferization/IR/Bufferization.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/Index/IR/IndexDialect.h"
#include "mlir/Dialect/Linalg/IR/Linalg.h"
#include "mlir/Dialect/Linalg/Passes.h"
#include "mlir/Dialect/MemRef/IR/MemRef.h"
#include "mlir/Dialect/MemRef/Transforms/Passes.h"
#include "mlir/Dialect/SCF/IR/SCF.h"
#include "mlir/Dialect/Tensor/IR/Tensor.h"
#include "mlir/Dialect/Transform/IR/TransformDialect.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Pass/PassManager.h"
#include "llvm/ADT/StringExtras.h"
#include "llvm/Support/SHA256.h"
#include "llvm/Support/raw_ostream.h"

namespace pia::codegen {

namespace {

constexpr llvm::StringLiteral kText = "pia.lower";
constexpr llvm::StringLiteral kAt = "pia.lower_at";
constexpr llvm::StringLiteral kName = "pia.lower_name";
constexpr llvm::StringLiteral kLowered = "pia.lowered";
constexpr llvm::StringLiteral kTmp = "pia_lowering";

std::string where(mlir::Location loc) {
  std::string out = "?";
  loc->walk([&](mlir::Location l) {
    auto f = mlir::dyn_cast<mlir::FileLineColLoc>(l);
    if (!f)
      return mlir::WalkResult::advance();
    out = f.getFilename().str() + ":" + std::to_string(f.getLine()) + ":" +
          std::to_string(f.getColumn());
    return mlir::WalkResult::interrupt();
  });
  return out;
}

std::string printed(mlir::Type t) {
  std::string s;
  llvm::raw_string_ostream os(s);
  t.print(os);
  return s;
}

bool isNameChar(char c) {
  return std::isalnum(static_cast<unsigned char>(c)) || c == '_' || c == '\'';
}

// The text with each `$name` replaced by the argument's SSA name in the
// wrapper and each `$name.type` by its core type. IRGen has already checked
// that every splice names a parameter, so a name with no argument here is
// one the signature rewrites took away.
mlir::FailureOr<std::string> splice(mlir::func::FuncOp f, llvm::StringRef text,
                                    mlir::Location at) {
  std::map<std::string, unsigned> argOf;
  for (unsigned i = 0; i < f.getNumArguments(); ++i)
    if (auto n = f.getArgAttrOfType<mlir::StringAttr>(i, kName))
      argOf.emplace(n.getValue().str(), i);
  std::string out;
  for (size_t i = 0; i < text.size(); ++i) {
    if (text[i] != '$') {
      out += text[i];
      continue;
    }
    size_t end = i + 1;
    while (end < text.size() && isNameChar(text[end]))
      ++end;
    std::string name = text.substr(i + 1, end - i - 1).str();
    bool type = text.substr(end).starts_with(".type") &&
                (end + 5 == text.size() || !isNameChar(text[end + 5]));
    auto arg = argOf.find(name);
    if (arg == argOf.end())
      return mlir::emitError(at)
             << "@lower splices '$" << name
             << "', which has no value in the compiled function";
    out += type ? printed(f.getArgument(arg->second).getType())
                : "%pia_arg" + std::to_string(arg->second);
    i = (type ? end + 5 : end) - 1;
  }
  return out;
}

// `func.func @pia_lowering(<the arguments>) -> <the results> { <text>
// return }`, with the text on lines of its own, so that line n + 1 of the
// wrapper is line n of the text.
std::string wrap(mlir::func::FuncOp f, const std::string &text) {
  std::string out = "func.func @" + kTmp.str() + "(";
  mlir::FunctionType ft = f.getFunctionType();
  for (unsigned i = 0; i < ft.getNumInputs(); ++i)
    out += (i ? ", %pia_arg" : "%pia_arg") + std::to_string(i) + ": " +
           printed(ft.getInput(i));
  out += ")";
  if (ft.getNumResults()) {
    out += " -> (";
    for (unsigned i = 0; i < ft.getNumResults(); ++i)
      out += (i ? ", " : "") + printed(ft.getResult(i));
    out += ")";
  }
  out += " {\n" + text + "\n";
  // A function that returns a value says what with its own `return`.
  if (!ft.getNumResults())
    out += "return\n";
  return out + "}\n";
}

// The ops a lowering uses, for the trust report. A named linalg op's body
// is generated from its definition, not written in the text, so its ops are
// not listed; a `linalg.generic`'s body is written, so its are.
std::vector<std::string> opsOf(mlir::func::FuncOp tmp) {
  std::set<std::string> ops;
  tmp.walk<mlir::WalkOrder::PreOrder>([&](mlir::Operation *op) {
    if (op == tmp.getOperation())
      return mlir::WalkResult::advance();
    llvm::StringRef name = op->getName().getStringRef();
    if (name != "func.return")
      ops.insert(name.str());
    if (mlir::isa<mlir::linalg::LinalgOp>(op) &&
        !mlir::isa<mlir::linalg::GenericOp>(op))
      return mlir::WalkResult::skip();
    return mlir::WalkResult::advance();
  });
  return {ops.begin(), ops.end()};
}

std::string sha256(llvm::StringRef text) {
  std::array<uint8_t, 32> digest = llvm::SHA256::hash(llvm::ArrayRef<uint8_t>(
      reinterpret_cast<const uint8_t *>(text.data()), text.size()));
  return llvm::toHex(digest, /*LowerCase=*/true);
}

mlir::FailureOr<Lowering> lowerOne(mlir::func::FuncOp f) {
  mlir::MLIRContext *ctx = f.getContext();
  llvm::StringRef text = f->getAttrOfType<mlir::StringAttr>(kText).getValue();
  mlir::Location at = f.getLoc();
  if (auto l = f->getAttrOfType<mlir::LocationAttr>(kAt))
    at = mlir::Location(l);
  mlir::FailureOr<std::string> spliced = splice(f, text, at);
  if (mlir::failed(spliced))
    return mlir::failure();
  std::string wrapper = wrap(f, *spliced);

  // MLIR's first diagnostic, which is the one that names the mistake; the
  // ones after it follow from it.
  std::string message;
  unsigned line = 0, column = 0;
  mlir::OwningOpRef<mlir::ModuleOp> parsed;
  {
    mlir::ScopedDiagnosticHandler handler(ctx, [&](mlir::Diagnostic &d) {
      if (!message.empty() ||
          d.getSeverity() != mlir::DiagnosticSeverity::Error)
        return mlir::success();
      message = d.str();
      d.getLocation()->walk([&](mlir::Location l) {
        auto fl = mlir::dyn_cast<mlir::FileLineColLoc>(l);
        if (!fl)
          return mlir::WalkResult::advance();
        line = fl.getLine();
        column = fl.getColumn();
        return mlir::WalkResult::interrupt();
      });
      return mlir::success();
    });
    mlir::ParserConfig config(ctx);
    parsed = mlir::parseSourceString<mlir::ModuleOp>(wrapper, config, "@lower");
  }
  auto tmp = parsed ? parsed->lookupSymbol<mlir::func::FuncOp>(kTmp)
                    : mlir::func::FuncOp();
  if (!tmp) {
    unsigned lines = 1 + llvm::count(*spliced, '\n');
    mlir::InFlightDiagnostic e = mlir::emitError(at)
                                 << "the @lower of '" << f.getSymName()
                                 << "' is not valid MLIR: " << message;
    if (line > 1 && line - 1 <= lines)
      e.attachNote() << "at line " << line - 1 << ", column " << column
                     << " of the MLIR after splicing:\n"
                     << *spliced;
    else
      e.attachNote() << "the MLIR is the body of a function with the "
                        "signature of '"
                     << f.getSymName()
                     << "', followed by 'return' when it returns nothing; "
                        "one that returns a value ends with its own "
                        "'return'";
    return mlir::failure();
  }

  Lowering l{f.getSymName().str(), where(at), *spliced, sha256(*spliced),
             opsOf(tmp)};
  // Errors in later passes, such as an op the pipeline cannot lower, point
  // at the attribute rather than at the parser's buffer.
  tmp.walk([&](mlir::Operation *op) { op->setLoc(at); });
  for (mlir::Block &b : tmp.getBody())
    for (mlir::BlockArgument a : b.getArguments())
      a.setLoc(at);
  f.getBody().takeBody(tmp.getBody());
  return l;
}

void unmark(mlir::func::FuncOp f) {
  f->removeAttr(kText);
  f->removeAttr(kAt);
  for (unsigned i = 0; i < f.getNumArguments(); ++i)
    f.removeArgAttr(i, kName);
}

} // namespace

void loadLoweringDialects(mlir::MLIRContext &ctx) {
  ctx.loadDialect<mlir::affine::AffineDialect, mlir::arith::ArithDialect,
                  mlir::bufferization::BufferizationDialect,
                  mlir::func::FuncDialect, mlir::index::IndexDialect,
                  mlir::linalg::LinalgDialect, mlir::memref::MemRefDialect,
                  mlir::scf::SCFDialect, mlir::tensor::TensorDialect,
                  mlir::transform::TransformDialect>();
}

mlir::LogicalResult applyLowerings(mlir::ModuleOp module, bool enabled,
                                   std::vector<Lowering> *applied) {
  llvm::SmallVector<mlir::func::FuncOp> marked;
  for (auto f : module.getOps<mlir::func::FuncOp>())
    if (f->hasAttr(kText))
      marked.push_back(f);
  if (marked.empty())
    return mlir::success();
  if (enabled)
    loadLoweringDialects(*module.getContext());
  bool ok = true, lowered = false;
  for (mlir::func::FuncOp f : marked) {
    if (enabled && !f.isExternal()) {
      mlir::FailureOr<Lowering> l = lowerOne(f);
      if (mlir::failed(l)) {
        ok = false;
      } else {
        lowered = true;
        if (applied)
          applied->push_back(std::move(*l));
      }
    }
    unmark(f);
  }
  if (lowered)
    module->setAttr(kLowered, mlir::UnitAttr::get(module.getContext()));
  return mlir::success(ok);
}

mlir::FailureOr<std::vector<Lowering>>
describeLowerings(mlir::ModuleOp module) {
  std::vector<Lowering> out;
  if (llvm::none_of(module.getOps<mlir::func::FuncOp>(),
                    [](mlir::func::FuncOp f) { return f->hasAttr(kText); }))
    return out;
  mlir::OwningOpRef<mlir::ModuleOp> copy = module.clone();
  eraseContracts(*copy);
  if (mlir::failed(lowerToCore(*copy)) ||
      mlir::failed(applyLowerings(*copy, /*enabled=*/true, &out)))
    return mlir::failure();
  return out;
}

bool takeLoweredMark(mlir::ModuleOp module) {
  return static_cast<bool>(module->removeAttr(kLowered));
}

void addLoweringPasses(mlir::OpPassManager &pm) {
  pm.addPass(mlir::createConvertLinalgToLoopsPass());
  pm.addPass(mlir::memref::createExpandStridedMetadataPass());
  pm.addPass(mlir::createLowerAffinePass());
}

} // namespace pia::codegen
