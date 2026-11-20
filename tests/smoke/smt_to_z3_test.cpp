// The planned verifier path end to end: build a goal in MLIR's smt dialect,
// export it to SMT-LIB, and have Z3 decide it (ADR 0011, ADR 0018).

#include <string>

#include "gtest/gtest.h"
#include "llvm/Support/raw_ostream.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/Dialect/SMT/IR/SMTDialect.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/MLIRContext.h"
#include "mlir/Parser/Parser.h"
#include "mlir/Target/SMTLIB/ExportSMTLIB.h"
#include "z3++.h"

namespace {

// Is there a u8 x with x + 1 < x (unsigned)? Yes: x = 255 wraps. This is the
// shape of the `bad` overflow example in docs/design.md.
constexpr const char *kWrapsGoal = R"mlir(
smt.solver () : () -> () {
  %x = smt.declare_fun "x" : !smt.bv<8>
  %one = smt.bv.constant #smt.bv<1> : !smt.bv<8>
  %sum = smt.bv.add %x, %one : !smt.bv<8>
  %lt = smt.bv.cmp ult %sum, %x : !smt.bv<8>
  smt.assert %lt
  smt.check sat {} unknown {} unsat {}
}
)mlir";

// Is there a u8 x with x & 0x0f > x? No.
constexpr const char *kMaskGoal = R"mlir(
smt.solver () : () -> () {
  %x = smt.declare_fun "x" : !smt.bv<8>
  %m = smt.bv.constant #smt.bv<15> : !smt.bv<8>
  %y = smt.bv.and %x, %m : !smt.bv<8>
  %gt = smt.bv.cmp ugt %y, %x : !smt.bv<8>
  smt.assert %gt
  smt.check sat {} unknown {} unsat {}
}
)mlir";

std::string ExportToSmtlib(const char *source) {
  mlir::MLIRContext context;
  context.loadDialect<mlir::smt::SMTDialect, mlir::func::FuncDialect>();
  mlir::OwningOpRef<mlir::ModuleOp> module =
      mlir::parseSourceString<mlir::ModuleOp>(source, &context);
  EXPECT_TRUE(module);
  if (!module) return "";
  std::string text;
  llvm::raw_string_ostream os(text);
  mlir::smt::SMTEmissionOptions options;
  options.emitReset = false;
  EXPECT_TRUE(mlir::succeeded(mlir::smt::exportSMTLIB(*module, os, options)));
  return text;
}

z3::check_result Solve(const std::string &smtlib) {
  z3::context ctx;
  z3::solver solver(ctx);
  // Drop the commands Z3's parser does not accept and check ourselves.
  std::string assertions;
  size_t pos = 0;
  while (pos < smtlib.size()) {
    size_t end = smtlib.find('\n', pos);
    if (end == std::string::npos) end = smtlib.size();
    std::string line = smtlib.substr(pos, end - pos);
    if (line.find("(check-sat)") == std::string::npos &&
        line.find("(reset)") == std::string::npos)
      assertions += line + "\n";
    pos = end + 1;
  }
  solver.from_string(assertions.c_str());
  return solver.check();
}

TEST(SmtToZ3, OverflowGoalIsSatisfiable) {
  std::string smtlib = ExportToSmtlib(kWrapsGoal);
  EXPECT_NE(smtlib.find("bvadd"), std::string::npos) << smtlib;
  EXPECT_EQ(Solve(smtlib), z3::sat);
}

TEST(SmtToZ3, MaskGoalIsUnsatisfiable) {
  EXPECT_EQ(Solve(ExportToSmtlib(kMaskGoal)), z3::unsat);
}

TEST(Z3, CppApiLinks) {
  z3::context ctx;
  z3::expr x = ctx.bv_const("x", 32);
  z3::solver solver(ctx);
  solver.add(x + 0 != x);
  EXPECT_EQ(solver.check(), z3::unsat);
}

}  // namespace
