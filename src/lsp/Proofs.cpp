#include "lsp/Proofs.h"

#include <cstdlib>

#include "irgen/IRGen.h"
#include "meta/Expand.h"
#include "mlir/IR/MLIRContext.h"
#include "syntax/Lexer.h"
#include "syntax/Parser.h"
#include "verify/Verifier.h"

namespace pia::lsp {

namespace {

// Line and column from the end of "file:line:col".
void parseWhere(const std::string &where, uint32_t &line, uint32_t &column) {
  size_t c = where.rfind(':');
  if (c == std::string::npos || c == 0) return;
  size_t l = where.rfind(':', c - 1);
  if (l == std::string::npos) return;
  line = static_cast<uint32_t>(std::strtoul(where.c_str() + l + 1, nullptr, 10));
  column = static_cast<uint32_t>(std::strtoul(where.c_str() + c + 1, nullptr, 10));
}

}  // namespace

ProofReport checkProofs(std::string_view source, const std::string &path,
                        unsigned timeoutMs) {
  ProofReport report;
  syntax::Diagnostics diags;
  syntax::NodePtr tree = syntax::parseProgram(
      source, diags, syntax::isLiterateFileName(path));
  if (diags.hasErrors()) return report;  // the front end reports these

  // Proofs are about the code after its metaprograms run (docs/meta.md).
  meta::expand(*tree, diags);
  if (diags.hasErrors()) {
    for (const syntax::Diagnostic &d : diags.errors())
      report.errors.push_back({d.loc.line, d.loc.column, d.message});
    return report;
  }

  mlir::MLIRContext ctx;
  ctx.disableMultithreading();
  mlir::OwningOpRef<mlir::ModuleOp> module =
      irgen::generate(*tree, path, ctx, diags);
  for (const syntax::Diagnostic &d : diags.errors())
    report.errors.push_back({d.loc.line, d.loc.column, d.message});
  if (!module) {
    if (report.errors.empty())
      report.errors.push_back(
          {1, 1, "internal error: the generated IR does not verify"});
    return report;
  }

  verify::Options options;
  options.timeoutMs = timeoutMs;
  for (const verify::Outcome &o : verify::verifyModule(*module, options)) {
    Goal g;
    switch (o.status) {
      case verify::Status::Proved: g.status = Goal::Status::Proved; break;
      case verify::Status::Failed: g.status = Goal::Status::Failed; break;
      case verify::Status::Skipped: g.status = Goal::Status::Skipped; break;
    }
    parseWhere(o.where, g.line, g.column);
    g.kind = contract::stringifyObligationKind(o.kind).str();
    g.claim = o.claim;
    g.method = o.method;
    for (const verify::ModelValue &v : o.counterexample)
      g.counterexample.emplace_back(v.name, v.value);
    report.goals.push_back(std::move(g));
  }
  return report;
}

}  // namespace pia::lsp
