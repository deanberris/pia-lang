// piac: the Pia compiler driver.
//
//   piac --emit=mlir file.pia       lower to the pia dialects and print (M4)
//   piac --verify file.pia          prove the program's obligations (M5)
//   piac --verify --emit=mlir ...   both; the report goes to stderr
//   piac --dump-smt file.pia        verify, printing each SMT query
//   piac --emit=obj -o f.o f.pia    verify, then compile to an object (M6)
//   piac --emit=asm|llvm|core ...   the same, stopping at assembly, LLVM IR
//                                   or the core MLIR dialects
//   piac --allow-unproved=SPEC ...  let --verify and codegen accept unproved
//                                   obligations:
//                                   all of them in function SPEC, or the ones
//                                   at SPEC = file:line or file:line:col
//   piac --solver-timeout=MS ...    give Z3 MS milliseconds per obligation
//                                   (default 10000)
//   piac --target=<triple> --cpu=<name> -O<n>   code generation options
//   piac --dump-ast file.pia        print the syntax tree
//   piac --dump-expanded file.pia   print it after metaprograms run (M7)
//   piac --meta-cycles=N ...        cap metaprogram expansion at N passes
//   piac --dump-tokens file.pia     print the token stream
//   piac --check file.pia           parse and report errors only
//   piac --fragment=contracts ...   parse a file of contract clauses
//   piac --comments --dump-ast ...  also print comment nodes (ADR 0029);
//                                   works with --dump-expanded too
//   piac --literate file.pia.md     read Markdown with code in ```pia blocks;
//                                   implied by a .pia.md file name
//
// Exit status: 0 on success, 1 on an error in the program or an obligation
// that does not hold, 2 on a usage error.
//
// Built with -DPIA_NO_MLIR, piac has only the front end and needs no LLVM
// (README, "Front end without Bazel").

#include <cstdlib>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include "meta/Expand.h"
#include "syntax/Lexer.h"
#include "syntax/Parser.h"
#include "syntax/Syntax.h"

#ifndef PIA_NO_MLIR
#include "codegen/Codegen.h"
#include "irgen/IRGen.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/FileSystem.h"
#include "verify/Verifier.h"
#include "llvm/Support/raw_ostream.h"
#include "mlir/IR/MLIRContext.h"
#endif

namespace {

int usage() {
  std::cerr << "usage: piac (--verify | --emit=mlir | --dump-ast | "
               "--dump-expanded | --dump-tokens | --check) "
               "[--fragment=contracts] [--meta-cycles=N]\n"
               "             [--literate] [--comments] [--solver-timeout=<ms>]\n"
               "             [--allow-unproved=<function>|<file:line[:col]>]... "
               "<file.pia>\n"
               "       piac --emit=(obj|asm|llvm|core) [-o <out>] "
               "[--target=<triple>] [--cpu=<name>] [-O<n>]\n"
               "             [--allow-unproved=<function>|<file:line[:col]>]... "
               "<file.pia>\n";
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

// Whether `--allow-unproved=spec` accepts the unproved obligation `o`: a
// spec without ':' names a function, and one with ':' is a location,
// "file:line" (any column) or "file:line:col".
bool allows(const std::string &spec, const pia::verify::Outcome &o) {
  if (spec.find(':') == std::string::npos) return o.function == spec;
  return o.where == spec || o.where.rfind(spec + ":", 0) == 0;
}

// The unproved obligations that no `--allow-unproved` accepts. Counts the
// accepted ones in `allowed`, and warns about each flag that accepts none.
std::vector<const pia::verify::Outcome *> unaccepted(
    const std::vector<pia::verify::Outcome> &outcomes,
    const std::vector<std::string> &allowUnproved, size_t &allowed) {
  std::vector<const pia::verify::Outcome *> out;
  std::vector<bool> used(allowUnproved.size(), false);
  for (const pia::verify::Outcome &o : outcomes) {
    if (o.status != pia::verify::Status::Skipped) continue;
    bool ok = false;
    for (size_t i = 0; i < allowUnproved.size(); ++i)
      if (allows(allowUnproved[i], o)) used[i] = ok = true;
    if (ok)
      ++allowed;
    else
      out.push_back(&o);
  }
  for (size_t i = 0; i < allowUnproved.size(); ++i)
    if (!used[i])
      std::cerr << "piac: warning: --allow-unproved=" << allowUnproved[i]
                << " matches no unproved obligation\n";
  return out;
}

std::string obligations(size_t n) {
  return std::to_string(n) + (n == 1 ? " obligation" : " obligations");
}

// Verifies, then compiles to `mode`'s output. Code is generated only when
// every obligation is proved. A failed one stops it with the verifier's
// report. So does an unproved one (v0 skips some, such as those in loops;
// docs/verifier.md, "Limits of v0"), unless `allowUnproved` accepts it.
int compile(mlir::ModuleOp module, const std::string &mode,
            const std::string &output, const pia::codegen::Options &options,
            const std::vector<std::string> &allowUnproved,
            const pia::verify::Options &verifyOptions) {
  using pia::verify::Outcome;
  using pia::verify::Status;
  std::vector<Outcome> outcomes =
      pia::verify::verifyModule(module, verifyOptions);
  bool failed = false;
  for (const Outcome &o : outcomes) failed |= o.status == Status::Failed;
  if (failed) {
    report(outcomes, std::cerr);
    return 1;
  }
  size_t allowed = 0;
  std::vector<const Outcome *> unproved =
      unaccepted(outcomes, allowUnproved, allowed);
  if (!unproved.empty()) {
    for (const Outcome *o : unproved)
      std::cerr << o->where << ": unproved: " << o->claim << " ["
                << o->method << "] in '" << o->function << "'\n";
    std::cerr << "piac: error: " << obligations(unproved.size())
              << " not proved, so no code was generated\n"
              << "piac: note: prove "
              << (unproved.size() == 1 ? "it" : "them")
              << ", or accept specific ones with "
                 "--allow-unproved=<function> or "
                 "--allow-unproved=<file:line[:col]>\n";
    return 1;
  }
  if (allowed > 0)
    std::cerr << "piac: warning: " << obligations(allowed)
              << " not proved, accepted by --allow-unproved; see "
                 "piac --verify\n";

  pia::codegen::eraseContracts(module);
  if (mlir::failed(pia::codegen::lowerToCore(module))) return 1;

  std::error_code ec;
  llvm::raw_fd_ostream out(output.empty() ? "-" : output, ec,
                           mode == "--emit=obj" ? llvm::sys::fs::OF_None
                                                : llvm::sys::fs::OF_Text);
  if (ec) {
    std::cerr << "piac: cannot write " << output << ": " << ec.message()
              << "\n";
    return 2;
  }
  if (mode == "--emit=core") {
    module.print(out);
    return 0;
  }
  if (mlir::failed(pia::codegen::lowerToLLVM(module))) return 1;
  llvm::LLVMContext llvmCtx;
  std::string error;
  std::unique_ptr<llvm::Module> llvmModule =
      pia::codegen::translate(module, llvmCtx, options, error);
  if (!llvmModule) {
    std::cerr << "piac: " << error << "\n";
    return 1;
  }
  if (mode == "--emit=llvm") {
    llvmModule->print(out, nullptr);
    return 0;
  }
  if (!pia::codegen::emitObject(*llvmModule, options, out, error,
                                mode == "--emit=asm")) {
    std::cerr << "piac: " << error << "\n";
    return 1;
  }
  return 0;
}
#endif

}  // namespace

int main(int argc, char **argv) {
  std::string mode, file, output;
  std::vector<std::string> allowUnproved;
  bool contracts = false, verify = false, dumpSmt = false;
  bool literate = false, showComments = false;
  pia::meta::Options meta;
  unsigned solverTimeoutMs = 0;  // 0: the verifier's default
#ifndef PIA_NO_MLIR
  pia::codegen::Options cg;
#endif
  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg == "--dump-ast" || arg == "--dump-expanded" ||
        arg == "--dump-tokens" || arg == "--check" ||
        arg == "--emit=mlir" || arg == "--emit=core" || arg == "--emit=llvm" ||
        arg == "--emit=asm" || arg == "--emit=obj")
      mode = arg;
    else if (arg == "-o" && i + 1 < argc)
      output = argv[++i];
#ifndef PIA_NO_MLIR
    else if (arg.rfind("--target=", 0) == 0)
      cg.triple = arg.substr(9);
    else if (arg.rfind("--cpu=", 0) == 0)
      cg.cpu = arg.substr(6);
    else if (arg.size() == 3 && arg.rfind("-O", 0) == 0 && arg[2] >= '0' &&
             arg[2] <= '3')
      cg.optLevel = arg[2] - '0';
#endif
    else if (arg.rfind("--allow-unproved=", 0) == 0) {
      if (arg.size() == 17) return usage();
      allowUnproved.push_back(arg.substr(17));
    }
    else if (arg.rfind("--solver-timeout=", 0) == 0) {
      char *end = nullptr;
      unsigned long ms = std::strtoul(arg.c_str() + 17, &end, 10);
      if (arg.size() == 17 || *end != '\0' || ms == 0 || ms > 3600000)
        return usage();
      solverTimeoutMs = static_cast<unsigned>(ms);
    }
    else if (arg == "--verify")
      verify = true;
    else if (arg == "--dump-smt")
      verify = dumpSmt = true;
    else if (arg == "--fragment=contracts")
      contracts = true;
    else if (arg == "--literate")
      literate = true;
    else if (arg == "--comments")
      showComments = true;
    else if (arg.rfind("--meta-cycles=", 0) == 0) {
      char *end = nullptr;
      long n = std::strtol(arg.c_str() + 14, &end, 10);
      if (*end != '\0' || n < 0) return usage();
      meta.maxCycles = static_cast<unsigned>(n);
    }
    else if (!arg.empty() && arg[0] == '-')
      return usage();
    else
      file = arg;
  }
  if (verify && mode.empty()) mode = "--verify";
  if (verify && mode != "--verify" && mode != "--emit=mlir") return usage();
  if (mode.empty() || file.empty()) return usage();
  if (pia::syntax::isLiterateFileName(file)) literate = true;
  if (showComments && mode != "--dump-ast" && mode != "--dump-expanded")
    return usage();
  if (literate && contracts) return usage();
  bool codegen = mode == "--emit=core" || mode == "--emit=llvm" ||
                 mode == "--emit=asm" || mode == "--emit=obj";
  if (codegen && verify) return usage();
  if (!allowUnproved.empty() && !codegen && !verify) return usage();
  if (mode == "--emit=obj" && output.empty()) return usage();
  if (!output.empty() && !codegen) return usage();
  if ((mode == "--emit=mlir" || mode == "--verify" || codegen) && contracts)
    return usage();
#ifdef PIA_NO_MLIR
  (void)solverTimeoutMs;
  if (mode == "--emit=mlir" || mode == "--verify" || codegen) {
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
    pia::syntax::LexOptions lex;
    lex.literate = literate;
    for (const pia::syntax::Token &t :
         pia::syntax::tokenize(source, diags, lex)) {
      std::cout << t.loc.line << ":" << t.loc.column << " "
                << pia::syntax::tokenKindName(t.kind);
      if (!t.text.empty()) std::cout << " " << t.text;
      std::cout << "\n";
    }
  } else {
    pia::syntax::NodePtr tree =
        contracts ? pia::syntax::parseContractFragment(source, diags)
                  : pia::syntax::parseProgram(source, diags, literate);
    if (!diags.hasErrors() && mode == "--dump-ast")
      pia::syntax::dump(std::cout, *tree, showComments);
    // Everything past the syntax tree sees the program after its
    // metaprograms have run (docs/meta.md).
    if (!diags.hasErrors() && !contracts && mode != "--dump-ast" &&
        mode != "--check")
      pia::meta::expand(*tree, diags, meta);
    if (!diags.hasErrors() && mode == "--dump-expanded")
      pia::syntax::dump(std::cout, *tree, showComments);
#ifndef PIA_NO_MLIR
    if (!diags.hasErrors() &&
        (mode == "--emit=mlir" || mode == "--verify" || codegen)) {
      mlir::MLIRContext ctx;
      auto module = pia::irgen::generate(*tree, file, ctx, diags);
      if (!module && !diags.hasErrors()) {
        std::cerr << "piac: internal error: the generated IR does not verify\n";
        return 1;
      }
      pia::verify::Options options;
      options.dumpSmt = dumpSmt;
      if (solverTimeoutMs) options.timeoutMs = solverTimeoutMs;
      if (module && codegen) {
        return compile(*module, mode, output, cg, allowUnproved, options);
      } else if (module && verify) {
        std::vector<pia::verify::Outcome> outcomes =
            pia::verify::verifyModule(*module, options);
        bool failed =
            report(outcomes, mode == "--emit=mlir" ? std::cerr : std::cout);
        if (mode == "--emit=mlir") module->print(llvm::outs());
        // A skipped goal is not proved, so it fails verification too unless
        // --allow-unproved accepts it, as it does for codegen.
        size_t allowed = 0;
        size_t unproved = unaccepted(outcomes, allowUnproved, allowed).size();
        if (!failed && unproved > 0)
          std::cerr << "piac: error: " << obligations(unproved)
                    << " not proved; accept specific ones with "
                       "--allow-unproved=<function> or "
                       "--allow-unproved=<file:line[:col]>\n";
        if (failed || unproved > 0) return 1;
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
