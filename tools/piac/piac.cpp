// piac: the Pia compiler driver.
//
//   piac --emit=mlir file.pia       lower to the pia dialects and print (M4)
//   piac --verify file.pia          prove the program's obligations (M5)
//   piac --verify --emit=mlir ...   both; the report goes to stderr
//   piac --dump-smt file.pia        verify, printing each SMT query
//   piac --dump-ast file.pia        print the syntax tree
//   piac --dump-tokens file.pia     print the token stream
//   piac --check file.pia           parse and report errors only
//   piac --fragment=contracts ...   parse a file of contract clauses
//
// Exit status: 0 on success, 1 on an error in the program or an obligation
// that does not hold, 2 on a usage error.
//
// Built with -DPIA_NO_MLIR, piac has only the front end and needs no LLVM
// (README, "Front end without Bazel").

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "syntax/Lexer.h"
#include "syntax/Parser.h"
#include "syntax/Syntax.h"

#ifndef PIA_NO_MLIR
#include "irgen/IRGen.h"
#include "verify/Verifier.h"
#include "llvm/Support/raw_ostream.h"
#include "mlir/IR/MLIRContext.h"
#endif

namespace {

int usage() {
  std::cerr << "usage: piac (--verify | --emit=mlir | --dump-ast | "
               "--dump-tokens | --check) "
               "[--fragment=contracts] <file.pia>\n";
  return 2;
}

#ifndef PIA_NO_MLIR
// Prints one line per obligation and a summary. Returns whether any failed.
bool report(const std::vector<pia::verify::Outcome> &outcomes,
            std::ostream &os) {
  using pia::verify::Status;
  int proved = 0, failed = 0, skipped = 0;
  for (const pia::verify::Outcome &o : outcomes) {
    switch (o.status) {
      case Status::Proved:
        ++proved;
        os << o.where << ": proved: " << o.claim << " [" << o.method << "]\n";
        break;
      case Status::Skipped:
        ++skipped;
        os << o.where << ": skipped: " << o.claim << " [" << o.method << "]\n";
        break;
      case Status::Failed:
        ++failed;
        os << o.where << ": failed: " << o.claim;
        if (o.method != "counterexample") os << " [" << o.method << "]";
        os << "\n";
        if (!o.counterexample.empty()) {
          os << "  counterexample:";
          const char *sep = " ";
          for (const pia::verify::ModelValue &v : o.counterexample) {
            os << sep << v.name << " = " << v.value;
            sep = ", ";
          }
          os << "\n";
        }
        break;
    }
  }
  os << proved << " proved, " << failed << " failed, " << skipped
     << " skipped\n";
  return failed > 0;
}
#endif

}  // namespace

int main(int argc, char **argv) {
  std::string mode, file;
  bool contracts = false, verify = false, dumpSmt = false;
  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg == "--dump-ast" || arg == "--dump-tokens" || arg == "--check" ||
        arg == "--emit=mlir")
      mode = arg;
    else if (arg == "--verify")
      verify = true;
    else if (arg == "--dump-smt")
      verify = dumpSmt = true;
    else if (arg == "--fragment=contracts")
      contracts = true;
    else if (!arg.empty() && arg[0] == '-')
      return usage();
    else
      file = arg;
  }
  if (verify && mode.empty()) mode = "--verify";
  if (verify && mode != "--verify" && mode != "--emit=mlir") return usage();
  if (mode.empty() || file.empty()) return usage();
  if ((mode == "--emit=mlir" || mode == "--verify") && contracts)
    return usage();
#ifdef PIA_NO_MLIR
  if (mode == "--emit=mlir" || mode == "--verify") {
    std::cerr << "piac: built without MLIR (-DPIA_NO_MLIR)\n";
    return 2;
  }
#endif

  std::ifstream in(file, std::ios::binary);
  if (!in) {
    std::cerr << "piac: cannot open " << file << "\n";
    return 2;
  }
  std::stringstream buf;
  buf << in.rdbuf();
  std::string source = buf.str();

  pia::syntax::Diagnostics diags;
  if (mode == "--dump-tokens") {
    for (const pia::syntax::Token &t : pia::syntax::tokenize(source, diags)) {
      std::cout << t.loc.line << ":" << t.loc.column << " "
                << pia::syntax::tokenKindName(t.kind);
      if (!t.text.empty()) std::cout << " " << t.text;
      std::cout << "\n";
    }
  } else {
    pia::syntax::NodePtr tree =
        contracts ? pia::syntax::parseContractFragment(source, diags)
                  : pia::syntax::parseProgram(source, diags);
    if (!diags.hasErrors() && mode == "--dump-ast")
      pia::syntax::dump(std::cout, *tree);
#ifndef PIA_NO_MLIR
    if (!diags.hasErrors() && (mode == "--emit=mlir" || mode == "--verify")) {
      mlir::MLIRContext ctx;
      auto module = pia::irgen::generate(*tree, file, ctx, diags);
      if (!module && !diags.hasErrors()) {
        std::cerr << "piac: internal error: the generated IR does not verify\n";
        return 1;
      }
      if (module && verify) {
        pia::verify::Options options;
        options.dumpSmt = dumpSmt;
        bool failed = report(pia::verify::verifyModule(*module, options),
                             mode == "--emit=mlir" ? std::cerr : std::cout);
        if (mode == "--emit=mlir") module->print(llvm::outs());
        if (failed) return 1;
      } else if (module) {
        module->print(llvm::outs());
      }
    }
#endif
  }
  if (diags.hasErrors()) {
    diags.print(std::cerr, file, source);
    return 1;
  }
  return 0;
}
