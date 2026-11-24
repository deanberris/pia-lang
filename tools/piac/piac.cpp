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
//                                   (default 600000, a safety net only)
//   piac --solver-rlimit=N ...      give Z3 a deterministic resource limit
//                                   of N per obligation (default
//                                   1200000000, as pia_object passes)
//   piac --solver-cost file.pia     --verify, also printing each proved
//                                   goal's Z3 resource count
//   piac --goal-times file.pia      --verify, also printing how long each
//                                   proved goal took to solve, in ms
//   piac --jobs=N ...               solve goals on N threads (default:
//                                   $PIA_JOBS if set, else one per core;
//                                   the report is the same)
//   piac --verify-only=SPEC ...     --verify only the goals SPEC selects: a
//                                   function, a module (file.pia) or a
//                                   location file:line[:col]; repeatable
//   piac --proof-cache=DIR ...      skip goals proved before, keyed by the
//                                   hash of each query
//   piac --slice ...                first try each goal with only the
//                                   assumptions it shares symbols with
//                                   (by default, only in a function with
//                                   a buffer of records, and only when
//                                   that drops a declaration)
//   piac --no-slice ...             always solve each goal's full query
//   piac --verify-stats ...         print a summary of the proof work, and
//                                   how long it took, to stderr; with
//                                   theories, each axiom's triggers and the
//                                   axioms each goal was given
//   piac --trust-report ...         with --verify, list the trusted items
//                                   the proofs rest on: today, the axioms
//                                   of theories with no model, and each
//                                   such theory's consistency check
//   piac --trust-report --why ...   also list, for each trusted axiom, the
//                                   goals whose proofs used it
//   piac --check-vacuity ...        with --verify, solve each goal proved
//                                   with a trusted axiom or an `assume`
//                                   again without its negation, and fail
//                                   it if its hypotheses contradict each
//                                   other (ADR 0036, step 7)
//   piac --explain-overloads=F:L .. for each overloaded or generic call on
//                                   line L of F, print its candidates,
//                                   why each removed one was, and which
//                                   one it chose, as notes on stderr
//   piac --no-lint[=NAME] ...       turn off every lint, or the one named
//                                   (ADR 0037, docs/idioms.md); repeatable
//   piac --costly-goal=N ...        warn about a goal whose Z3 resource
//                                   count is N or more (default 10% of the
//                                   rlimit); 0 turns the warning off
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

#include <algorithm>
#include <cstdlib>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

#include "meta/Expand.h"
#include "syntax/Interfaces.h"
#include "syntax/Lexer.h"
#include "syntax/Lint.h"
#include "syntax/Parser.h"
#include "syntax/Syntax.h"

#ifndef PIA_NO_MLIR
#include "cert/Certificate.h"
#include "codegen/Codegen.h"
#include "dialect/PiaDialect.h"
#include "gpu/Spirv.h"
#include "irgen/IRGen.h"
#include "mlir/Dialect/Func/IR/FuncOps.h"
#include "mlir/IR/Diagnostics.h"
#include "mlir/IR/MLIRContext.h"
#include "mlir/Parser/Parser.h"
#include "verify/Verifier.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/SourceMgr.h"
#include "llvm/Support/raw_ostream.h"
#endif

namespace {

int usage() {
  std::cerr
      << "usage: piac (--verify | --emit=mlir | --dump-ast | "
         "--dump-expanded | --dump-tokens | --check) "
         "[--fragment=contracts] [--meta-cycles=N]\n"
         "             [--literate] [--comments] [--solver-timeout=<ms>]\n"
         "             [--solver-rlimit=<n>] [--solver-cost] [--goal-times] "
         "[--jobs=<n>]\n"
         "             "
         "[--verify-only=<function>|<file.pia>|<file:line[:col]>]...\n"
         "             [--proof-cache=<dir>] [--slice | --no-slice] "
         "[--verify-stats] [--trust-report [--why]] [--check-vacuity]\n"
         "             [--explain-overloads=<file:line>]\n"
         "             [--no-lint[=<name>]]... [--costly-goal=<n>]\n"
         "             [--allow-unproved=<function>|<file:line[:col]>]... "
         "<file.pia>\n"
         "       piac --emit=interface -o <dir> <file.pia>\n"
         "       piac --emit=spirv -o <out.spv> <file.mlir>\n"
         "       piac --emit=(obj|asm|llvm|core) [-o <out>] "
         "[--target=<triple>] [--cpu=<name>] [-O<n>]\n"
         "             [--allow-unproved=<function>|<file:line[:col]>]... "
         "<file.pia>\n"
         "       Every mode but --emit=interface takes "
         "[--iface-path=<dir>]...\n";
  return 2;
}

#ifndef PIA_NO_MLIR
// Parses an MLIR file holding a gpu.module, lowers it to SPIR-V and writes
// the binary to `output`.
int emitSpirv(const std::string &file, const std::string &output) {
  mlir::DialectRegistry registry;
  pia::gpu::registerDialects(registry);
  mlir::MLIRContext ctx(registry);
  auto buffer = llvm::MemoryBuffer::getFile(file);
  if (!buffer) {
    std::cerr << file << ": " << buffer.getError().message() << "\n";
    return 1;
  }
  llvm::SourceMgr sm;
  sm.AddNewSourceBuffer(std::move(*buffer), llvm::SMLoc());
  mlir::SourceMgrDiagnosticHandler diagnostics(sm, &ctx);
  mlir::OwningOpRef<mlir::ModuleOp> module =
      mlir::parseSourceFile<mlir::ModuleOp>(sm, &ctx);
  if (!module)
    return 1;
  if (mlir::failed(pia::gpu::lowerToSpirv(*module)))
    return 1;
  llvm::SmallVector<uint32_t> binary;
  if (mlir::failed(pia::gpu::serializeSpirv(*module, binary)))
    return 1;
  std::error_code ec;
  llvm::raw_fd_ostream out(output, ec, llvm::sys::fs::OF_None);
  if (ec) {
    std::cerr << output << ": " << ec.message() << "\n";
    return 1;
  }
  out.write(reinterpret_cast<const char *>(binary.data()),
            binary.size() * sizeof(uint32_t));
  return 0;
}
#endif

// Which lints are on: all but those --no-lint names, or none.
struct LintSwitch {
  bool all = true;
  std::vector<std::string> off;
  bool on(const std::string &name) const {
    if (!all) return false;
    for (const std::string &o : off)
      if (o == name) return false;
    return true;
  }
};

#ifndef PIA_NO_MLIR
// Prints one line per obligation and a summary. Returns whether any failed.
bool report(const std::vector<pia::verify::Outcome> &outcomes, std::ostream &os,
            bool showCost = false, const pia::verify::Stats *stats = nullptr,
            bool showMs = false) {
  using pia::verify::Status;
  int proved = 0, failed = 0, skipped = 0;
  for (const pia::verify::Outcome &o : outcomes) {
    switch (o.status) {
      case Status::Proved:
        ++proved;
        // A goal of a generic's proof over sorts says so, whatever proved
        // it (ADR 0043).
        os << o.where << ": proved: " << o.claim << " ["
           << (o.generic ? "generic" : o.method) << "]";
        if (showCost && o.cost) os << " (cost " << o.cost << ")";
        // Wall-clock time depends on the machine and the load; cost does
        // not. Both are wanted when a proof is slow but cheap.
        if (showMs && o.ms > 0)
          os << " (" << static_cast<long long>(o.ms) << " ms)";
        os << "\n";
        break;
      case Status::Skipped:
        ++skipped;
        os << o.where << ": skipped: " << o.claim << " [" << o.method << "]\n";
        break;
      case Status::Failed:
        ++failed;
        os << o.where << ": failed: " << o.claim;
        if (o.method != "counterexample") os << " [" << o.method << "]";
        if (o.generic) os << " [generic]";
        os << "\n";
        // A goal with no values to show, false in a model (ADR 0036).
        if (o.counterexample.empty() && !o.model.empty())
          os << "  false in the model '" << o.model << "'\n";
        if (!o.counterexample.empty()) {
          os << "  counterexample";
          if (!o.model.empty()) os << " in the model '" << o.model << "'";
          os << ":";
          const char *sep = " ";
          for (const pia::verify::ModelValue &v : o.counterexample) {
            os << sep << v.name << " = " << v.value;
            sep = ", ";
          }
          os << "\n";
        }
        if (!o.hint.empty()) os << "  hint: " << o.hint << "\n";
        break;
    }
  }
  // The generics proved only at their instances, and why (ADR 0043).
  if (stats)
    for (const auto &n : stats->notParametric)
      os << n[0] << ": not proved generically: '" << n[1]
         << "' is proved at each instance, since " << n[2] << " [generic]\n";
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

// The costly_goal lint (ADR 0037): a goal the solver found hard. It reads
// the cost each goal took, so it runs after verification, not on syntax.
void warnCostly(const std::vector<pia::verify::Outcome> &outcomes,
                unsigned long long threshold, unsigned rlimit) {
  if (threshold == 0) return;
  for (const pia::verify::Outcome &o : outcomes) {
    if (o.status != pia::verify::Status::Proved || o.cost < threshold) continue;
    std::string advice;
    if (o.claim.find("postcondition") != std::string::npos ||
        o.claim.find("invariant") != std::string::npos ||
        o.claim.find("assertion") != std::string::npos)
      advice = "split it into smaller facts proved one at a time with "
               "'assert', or prove the hard step once as a 'let lemma' and "
               "call it";
    else if (o.claim.find("precondition") != std::string::npos)
      advice = "give the callee's parameters range types so the argument's "
               "type carries the fact, or state the bound where the argument "
               "is made";
    else
      advice = "bound the values it depends on with range types so intervals "
               "decide it, or move the step into a function whose contract "
               "states only what it needs";
    std::cerr << o.where << ": warning: proving that " << o.claim << " in '"
              << o.function << "' cost " << o.cost;
    if (rlimit)
      std::cerr << " (" << (o.cost * 100 / rlimit) << "% of the solver's limit)";
    std::cerr << "; " << advice << ". Re-run it alone with --verify-only="
              << o.where << " [costly_goal]\n";
  }
}

std::string obligations(size_t n) {
  return std::to_string(n) + (n == 1 ? " obligation" : " obligations");
}

// Verifies, then compiles to `mode`'s output. Code is generated only when
// every obligation is proved. A failed one stops it with the verifier's
// report. So does an unproved one (v0 skips some, such as those in loops;
// docs/verifier.md, "Limits of v0"), unless `allowUnproved` accepts it.
// One line, `verify-stats: key=value ...`, that tools/bench reads.
void printStats(const pia::verify::Stats &st) {
  std::cerr << "verify-stats: goals=" << st.goals
            << " unselected=" << st.unselected
            << " intervals=" << st.intervals << " skipped=" << st.skipped
            << " solved=" << st.solved << " cached=" << st.cached
            << " sliced=" << st.sliced << " unsliced=" << st.unsliced
            << " threads=" << st.threads << " cost=" << st.cost
            << " encode_ms=" << static_cast<long long>(st.encodeMs)
            << " solve_ms=" << static_cast<long long>(st.solveMs)
            << " type=" << st.typeGoals << " type_smt=" << st.typeSmt
            << " type_cost=" << st.typeCost
            << " contract=" << st.contractGoals
            << " contract_smt=" << st.contractSmt
            << " contract_cost=" << st.contractCost
            << " generic=" << st.genericGoals << " instances=" << st.instances
            << "\n";
  // Theories (ADR 0036): each axiom's triggers. Their own prefix keeps the
  // line above the only `verify-stats:` line.
  // --check-vacuity's extra queries, on a line of their own.
  if (st.vacuityChecks)
    std::cerr << "verify-stats-vacuity: checks=" << st.vacuityChecks
              << " vacuous=" << st.vacuous << " unknown=" << st.vacuityUnknown
              << " cost=" << st.vacuityCost << "\n";
  for (const auto &[axiom, triggers] : st.triggers) {
    std::cerr << "verify-stats-axiom: " << axiom << " triggers=";
    for (size_t i = 0; i < triggers.size(); ++i)
      std::cerr << (i ? " | " : "") << "(" << triggers[i] << ")";
    std::cerr << "\n";
  }
}

// The axioms each goal over a theory was given (ADR 0036).
void printGoalAxioms(const std::vector<pia::verify::Outcome> &outcomes) {
  for (const pia::verify::Outcome &o : outcomes) {
    if (o.axioms.empty() && !o.fallback) continue;
    std::cerr << "verify-stats-goal: " << o.where << " axioms=";
    for (size_t i = 0; i < o.axioms.size(); ++i)
      std::cerr << (i ? "," : "") << o.axioms[i];
    if (o.fallback) std::cerr << " fallback=all";
    // The axioms the proof used, from its unsat core (ADR 0036).
    if (o.status == pia::verify::Status::Proved) {
      std::cerr << " used=";
      for (size_t i = 0; i < o.axiomsUsed.size(); ++i)
        std::cerr << (i ? "," : "") << o.axiomsUsed[i];
    }
    std::cerr << "\n";
  }
}

// `--trust-report`: what the program's proofs rest on without proof: the
// axioms of theories with no model (ADR 0036), with each such theory's
// consistency check, foreign functions' contracts, `unsafe` calls (#55)
// and `assume`s (ADR 0023).
void printTrustReport(mlir::ModuleOp module, const pia::verify::Stats &stats,
                      const std::vector<pia::verify::Outcome> &outcomes,
                      bool why, std::ostream &os) {
  // Each trusted theory's consistency check.
  std::map<std::string, const pia::verify::TheoryCheck *> checks;
  for (const pia::verify::TheoryCheck &c : stats.theories) {
    checks[c.theory] = &c;
    os << c.where << ": the theory '" << c.theory << "' is ";
    if (c.status == "consistent")
      os << "consistent: the solver found a witness, a model of its axioms";
    else if (c.status == "inconsistent")
      os << "inconsistent: its axioms contradict each other";
    else
      os << "unchecked: the solver could not decide whether its axioms are "
            "consistent"
         << (c.reason.empty() ? "" : " (" + c.reason + ")");
    os << "\n";
  }
  // `import T trusting`: the grants.
  if (auto grants = module->getAttrOfType<mlir::ArrayAttr>("pia.trusting"))
    for (mlir::Attribute g : grants) {
      llvm::StringRef text = mlir::cast<mlir::StringAttr>(g).getValue();
      auto [theory, where] = text.split(' ');
      os << where.str() << ": trusting the theory '" << theory.str() << "'\n";
    }
  // What each goal rests on: the axioms its proof used, and, since a call
  // to a lemma assumes what the lemma proved, the axioms behind every
  // lemma its function calls, transitively.
  std::map<std::string, std::set<std::string>> behind;  // function -> axioms
  for (const pia::verify::Outcome &o : outcomes)
    if (o.status == pia::verify::Status::Proved)
      behind[o.function].insert(o.axiomsUsed.begin(), o.axiomsUsed.end());
  std::map<std::string, std::set<std::string>> calls;
  for (auto f : module.getOps<mlir::func::FuncOp>())
    f.walk([&](mlir::func::CallOp c) {
      calls[f.getSymName().str()].insert(c.getCallee().str());
    });
  for (bool changed = true; changed;) {
    changed = false;
    for (auto &[f, callees] : calls)
      for (const std::string &g : callees)
        for (const std::string &a : behind[g])
          changed |= behind[f].insert(a).second;
  }
  auto restsOn = [&](const pia::verify::Outcome &o) {
    std::set<std::string> all(o.axiomsUsed.begin(), o.axiomsUsed.end());
    for (const std::string &g : calls[o.function])
      all.insert(behind[g].begin(), behind[g].end());
    return all;
  };
  // `--why`: the goals whose proofs used a trusted axiom or `assume`
  // (ADR 0036).
  auto usedBy = [&](const std::string &name) {
    std::vector<std::string> users;
    for (const pia::verify::Outcome &o : outcomes)
      if (o.status == pia::verify::Status::Proved && restsOn(o).count(name))
        users.push_back(o.where);
    if (users.empty()) {
      os << "  used by no proved goal\n";
    } else {
      os << "  used by:";
      for (size_t i = 0; i < users.size(); ++i)
        os << (i ? ", " : " ") << users[i];
      os << "\n";
    }
  };
  unsigned n = 0, assumes = 0;
  std::set<std::string> trustedAxioms;  // and `assume file:line:col`
  for (auto f : module.getOps<mlir::func::FuncOp>()) {
    if (auto sym = f->getAttrOfType<mlir::StringAttr>("pia.extern")) {
      os << pia::verify::formatLoc(f.getLoc())
         << ": trusted: the contract of the foreign function '"
         << f.getSymName().str() << "' (C symbol '" << sym.getValue().str()
         << "')\n";
      ++n;
    }
    f.walk([&](mlir::func::CallOp c) {
      if (!c->hasAttr("pia.unsafe")) return;
      os << pia::verify::formatLoc(c.getLoc()) << ": trusted: the unsafe call "
         << "of '" << c.getCallee().str() << "'\n";
      ++n;
    });
    f.walk([&](pia::ViewOp v) {
      os << pia::verify::formatLoc(v.getLoc()) << ": trusted: the unsafe view "
         << "of foreign memory in '" << f.getSymName().str() << "'\n";
      ++n;
    });
    // An `assume` is trusted (ADR 0023): the goals whose proofs used it
    // are those whose unsat core names it.
    f.walk([&](pia::contract::AssumeOp a) {
      std::string where = pia::verify::formatLoc(a.getLoc());
      std::string name = "assume " + where;
      trustedAxioms.insert(name);
      ++assumes;
      os << where << ": trusted: the 'assume' in '" << f.getSymName().str()
         << "'\n";
      if (why) usedBy(name);
      ++n;
    });
    if (!f->hasAttr(pia::PiaDialect::getAxiomAttrName())) continue;
    // A theory with a model is proved consistent by it: nothing trusted.
    if (f->hasAttr("pia.modelled")) continue;
    std::string theory;
    if (auto t = f->getAttrOfType<mlir::StringAttr>("pia.theory"))
      theory = t.getValue().str();
    std::string name = f.getSymName().str();
    trustedAxioms.insert(name);
    os << pia::verify::formatLoc(f.getLoc()) << ": trusted: the axiom '"
       << name << "', since the theory '" << theory << "' has no model\n";
    if (why) usedBy(name);
    ++n;
  }
  os << n << (n == 1 ? " trusted item\n" : " trusted items\n");
  if (why) {
    // A goal that used no trusted axiom is fully proved, whatever its
    // file trusts.
    unsigned proved = 0, resting = 0;
    for (const pia::verify::Outcome &o : outcomes) {
      if (o.status != pia::verify::Status::Proved) continue;
      ++proved;
      for (const std::string &a : restsOn(o))
        if (trustedAxioms.count(a)) {
          ++resting;
          break;
        }
    }
    os << resting << " of " << proved << " proved goals rest on a trusted "
       << (assumes ? "axiom or 'assume'" : "axiom") << "; the other "
       << (proved - resting) << " are fully proved\n";
  }
}

int compile(mlir::ModuleOp module, const std::string &mode,
            const std::string &output, const pia::codegen::Options &options,
            const std::vector<std::string> &allowUnproved,
            const pia::verify::Options &verifyOptions, bool verifyStats) {
  using pia::verify::Outcome;
  using pia::verify::Status;
  pia::verify::Stats stats;
  if (mlir::failed(pia::verify::resolveOverloads(module, verifyOptions))) {
    std::cerr << "piac: internal error: cannot choose between overloads\n";
    return 1;
  }
  std::vector<Outcome> outcomes =
      pia::verify::verifyModule(module, verifyOptions, &stats);
  if (verifyStats) {
    printStats(stats);
    printGoalAxioms(outcomes);
  }
  bool failed = false;
  for (const Outcome &o : outcomes) failed |= o.status == Status::Failed;
  if (failed) {
    report(outcomes, std::cerr, false, &stats);
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
  // Only what a module exports gets a C entry point (ADR 0039).
  if (mlir::failed(pia::codegen::lowerToLLVM(module, /*exportsOnly=*/true)))
    return 1;
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
  std::vector<std::string> ifacePaths;
  bool contracts = false, verify = false, dumpSmt = false;
  bool literate = false, showComments = false;
  pia::meta::Options meta;
  // Whether a goal is proved must not depend on load: since goals are
  // solved on every core, a wall-clock limit would turn proofs into
  // timeouts on a busy machine. So the deterministic rlimit decides, as in
  // pia_object, and the timeout is only a safety net (ADR 0032).
  unsigned solverTimeoutMs = 600000;
  unsigned solverRlimit = 1200000000;
  unsigned memoryBallastMb = 0;
  bool solverCost = false;
  bool goalTimes = false;
  unsigned jobs = 0;  // 0: one per core
  std::vector<std::string> verifyOnly;
  std::string proofCache;
  int slice = 0;  // 0 automatic, 1 --slice, -1 --no-slice
  bool verifyStats = false;
  bool checkVacuity = false;
  bool trustReport = false;
  bool trustWhy = false;
  std::string explainFile;
  unsigned explainLine = 0;
  LintSwitch lints;
  long long costlyGoal = -1;  // -1: 10% of the rlimit
#ifndef PIA_NO_MLIR
  pia::codegen::Options cg;
#endif
  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg == "--dump-ast" || arg == "--dump-expanded" ||
        arg == "--dump-tokens" || arg == "--check" || arg == "--emit=mlir" ||
        arg == "--emit=core" || arg == "--emit=llvm" || arg == "--emit=asm" ||
        arg == "--emit=obj" || arg == "--emit=interface" ||
        arg == "--emit=spirv")
      mode = arg;
    else if (arg.rfind("--iface-path=", 0) == 0) {
      if (arg.size() == 13) return usage();
      ifacePaths.push_back(arg.substr(13));
    }
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
    else if (arg.rfind("--solver-rlimit=", 0) == 0) {
      char *end = nullptr;
      unsigned long n = std::strtoul(arg.c_str() + 16, &end, 10);
      if (arg.size() == 16 || *end != '\0' || n == 0 || n > 4000000000UL)
        return usage();
      solverRlimit = static_cast<unsigned>(n);
    }
    else if (arg.rfind("--memory-ballast=", 0) == 0) {
      // Test only: hold this many megabytes of Z3 terms before solving.
      char *end = nullptr;
      unsigned long n = std::strtoul(arg.c_str() + 17, &end, 10);
      if (arg.size() == 17 || *end != '\0' || n == 0 || n > 65536)
        return usage();
      memoryBallastMb = static_cast<unsigned>(n);
    }
    else if (arg.rfind("--jobs=", 0) == 0) {
      char *end = nullptr;
      unsigned long n = std::strtoul(arg.c_str() + 7, &end, 10);
      if (arg.size() == 7 || *end != '\0' || n == 0 || n > 4096)
        return usage();
      jobs = static_cast<unsigned>(n);
    }
    else if (arg.rfind("--verify-only=", 0) == 0) {
      if (arg.size() == 14) return usage();
      verifyOnly.push_back(arg.substr(14));
      verify = true;
    }
    else if (arg.rfind("--proof-cache=", 0) == 0) {
      if (arg.size() == 14) return usage();
      proofCache = arg.substr(14);
    }
    else if (arg == "--slice")
      slice = 1;
    else if (arg == "--no-slice")
      slice = -1;
    else if (arg == "--verify-stats")
      verifyStats = true;
    else if (arg == "--check-vacuity")
      verify = checkVacuity = true;
    else if (arg == "--trust-report")
      trustReport = true;
    else if (arg == "--why")
      trustWhy = true;
    else if (arg.rfind("--explain-overloads=", 0) == 0) {
      std::string spec = arg.substr(20);
      size_t colon = spec.rfind(':');
      if (colon == std::string::npos || colon == 0) return usage();
      char *end = nullptr;
      unsigned long line = std::strtoul(spec.c_str() + colon + 1, &end, 10);
      if (*end != '\0' || line == 0 || colon + 1 == spec.size())
        return usage();
      explainFile = spec.substr(0, colon);
      explainLine = static_cast<unsigned>(line);
    }
    else if (arg == "--no-lint")
      lints.all = false;
    else if (arg.rfind("--no-lint=", 0) == 0) {
      std::string name = arg.substr(10);
      bool known = false;
      for (std::string_view n : pia::syntax::lintNames()) known |= n == name;
      if (!known) {
        std::cerr << "piac: no lint is named '" << name << "'\n";
        return usage();
      }
      lints.off.push_back(name);
    }
    else if (arg.rfind("--costly-goal=", 0) == 0) {
      char *end = nullptr;
      unsigned long long n = std::strtoull(arg.c_str() + 14, &end, 10);
      if (arg.size() == 14 || *end != '\0') return usage();
      costlyGoal = static_cast<long long>(n);
    }
    else if (arg == "--solver-cost")
      verify = solverCost = true;
    else if (arg == "--goal-times")
      verify = goalTimes = true;
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
    else if (!file.empty()) {
      // A second input would silently replace the first, and an argument
      // like " --verify-only=f", a flag after a space, is one: a shell
      // that does not split a variable passes it so, and the selection
      // is lost without a word (#376).
      std::cerr << "piac: error: more than one input file: '" << file
                << "' and '" << arg << "'";
      for (const std::string &a : {file, arg}) {
        size_t first = a.find_first_not_of(" \t");
        if (first != std::string::npos && first > 0 && a[first] == '-') {
          std::cerr << "; '" << a.substr(first)
                    << "' looks like a flag with a space before it, as an "
                       "unsplit shell variable passes it";
          break;
        }
      }
      std::cerr << "\n";
      return 2;
    } else
      file = arg;
  }
  if (verify && mode.empty()) mode = "--verify";
  if (verify && mode != "--verify" && mode != "--emit=mlir") return usage();
  if (mode.empty() || file.empty()) return usage();
#ifndef PIA_NO_MLIR
  // A hand-written gpu.module, lowered to a SPIR-V binary (ADR 0068, step
  // 1). Step 3 makes the gpu.module from @place(gpu) spreads.
  if (mode == "--emit=spirv") {
    if (output.empty() || verify)
      return usage();
    return emitSpirv(file, output);
  }
#endif
  if (pia::syntax::isLiterateFileName(file)) literate = true;
  if (showComments && mode != "--dump-ast" && mode != "--dump-expanded")
    return usage();
  if (literate && contracts) return usage();
  bool codegen = mode == "--emit=core" || mode == "--emit=llvm" ||
                 mode == "--emit=asm" || mode == "--emit=obj";
  // A partial proof never justifies code, so --verify-only implies --verify.
  if (codegen && verify) return usage();
  if (!allowUnproved.empty() && !codegen && !verify) return usage();
  if (mode == "--emit=obj" && output.empty()) return usage();
  bool emitInterface = mode == "--emit=interface";
  if (emitInterface && (output.empty() || verify || contracts ||
                        !ifacePaths.empty()))
    return usage();
  // With no --jobs, $PIA_JOBS caps the solver threads, so a machine running
  // many piac processes at once (a Bazel test suite, several worktrees) can
  // keep their total near its core count. ~/.bazelrc on a shared machine
  // passes it to tests with --test_env.
  if (jobs == 0) {
    if (const char *env = std::getenv("PIA_JOBS")) {
      char *end = nullptr;
      unsigned long n = std::strtoul(env, &end, 10);
      if (*env != '\0' && *end == '\0' && n > 0 && n <= 4096)
        jobs = static_cast<unsigned>(n);
    }
  }
  if (!output.empty() && !codegen && !emitInterface) return usage();
  if ((mode == "--emit=mlir" || mode == "--verify" || codegen) && contracts)
    return usage();
#ifdef PIA_NO_MLIR
  (void)solverTimeoutMs;
  (void)solverRlimit;
  (void)solverCost;
  (void)goalTimes;
  (void)jobs;
  (void)slice;
  (void)verifyStats;
  (void)trustReport;
  (void)trustWhy;
  (void)explainLine;
  (void)costlyGoal;
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
    // An interface artifact is the interface as written (ADR 0039), so it
    // needs neither metaprograms nor the verifier.
    if (!diags.hasErrors() && emitInterface) {
      for (const pia::syntax::InterfaceArtifact &a :
           pia::syntax::interfaceArtifacts(*tree, source, literate, diags)) {
        std::string path = output + "/" + a.fileName();
        std::ofstream out(path, std::ios::binary);
        out << a.text;
        if (!out) {
          std::cerr << "piac: cannot write " << path << "\n";
          return 2;
        }
      }
    }
    // Lints read the program as written, before metaprograms run, so they
    // point at the user's code and not at generated code.
    if (!diags.hasErrors() && !contracts &&
        (mode == "--check" || mode == "--verify" || mode == "--emit=mlir" ||
         mode == "--emit=core" || mode == "--emit=llvm" ||
         mode == "--emit=asm" || mode == "--emit=obj"))
      for (const pia::syntax::Lint &l : pia::syntax::lint(*tree, source))
        if (lints.on(l.name)) pia::syntax::printLint(std::cerr, l, file, source);
    // Everything past the syntax tree sees the program after its
    // metaprograms have run (docs/meta.md).
    // Imports bring in the functions of other modules' interfaces, as
    // items whose bodies are elsewhere (ADR 0039).
    // An object defines a witness for each interface its module provides
    // and references one for each it imports (docs/abi.md, Layer 1).
    std::vector<pia::syntax::InterfaceArtifact> provided, imported;
    if (!diags.hasErrors() && codegen) {
      pia::syntax::Diagnostics ignored; // the module check reports them
      provided =
          pia::syntax::interfaceArtifacts(*tree, source, literate, ignored);
    }
    if (!diags.hasErrors() && !contracts && mode != "--dump-ast" &&
        mode != "--check" && !emitInterface)
      pia::syntax::resolveImports(*tree, ifacePaths, diags, &imported);
#ifndef PIA_NO_MLIR
    for (const pia::syntax::InterfaceArtifact &a : provided)
      cg.providedWitnesses.push_back(
          pia::codegen::witnessSymbol(a.module, a.name, a.text));
    for (const pia::syntax::InterfaceArtifact &a : imported)
      cg.requiredWitnesses.push_back(
          pia::codegen::witnessSymbol(a.module, a.name, a.text));
    if (codegen) {
      pia::cert::Certificate cert;
      if (!tree->kids.empty() &&
          tree->kids[0]->kind == pia::syntax::NodeKind::ModuleHeader)
        cert.module = tree->kids[0]->text;
      for (const pia::syntax::InterfaceArtifact &a : provided)
        cert.provides.push_back(
            {a.module + "." + a.name, pia::cert::interfaceHash(a.text)});
      for (const pia::syntax::InterfaceArtifact &a : imported)
        cert.requires_.push_back(
            {a.module + "." + a.name, pia::cert::interfaceHash(a.text)});
      cg.certificate = pia::cert::encode(cert);
    }
#endif
    if (!diags.hasErrors() && !contracts && mode != "--dump-ast" &&
        mode != "--check" && !emitInterface)
      pia::meta::expand(*tree, diags, meta);
    if (!diags.hasErrors() && mode == "--dump-expanded")
      pia::syntax::dump(std::cout, *tree, showComments);
#ifndef PIA_NO_MLIR
    if (!diags.hasErrors() &&
        (mode == "--emit=mlir" || mode == "--verify" || codegen)) {
      mlir::MLIRContext ctx;
      pia::irgen::Options irgenOptions;
      irgenOptions.source = source;
      irgenOptions.triple = cg.triple;
      std::vector<pia::syntax::Diagnostic> explanations;
      auto sameFile = [&](const std::string &a, const std::string &b) {
        auto base = [](const std::string &p) {
          size_t slash = p.find_last_of('/');
          return slash == std::string::npos ? p : p.substr(slash + 1);
        };
        return a == b || base(a) == base(b);
      };
      if (explainLine && sameFile(explainFile, file)) {
        irgenOptions.explainLine = explainLine;
        irgenOptions.explanations = &explanations;
      }
      auto module = pia::irgen::generate(*tree, file, ctx, diags, irgenOptions);
      for (const pia::syntax::Diagnostic &d : explanations)
        std::cerr << file << ":" << d.loc.line << ":" << d.loc.column
                  << ": note: " << d.message << "\n";
      if (!module && !diags.hasErrors()) {
        std::cerr << "piac: internal error: the generated IR does not verify\n";
        return 1;
      }
      pia::verify::Options options;
      options.dumpSmt = dumpSmt;
      options.timeoutMs = solverTimeoutMs;
      options.rlimit = solverRlimit;
      // Each goal's cost is always kept, for the costly_goal lint; the
      // report shows it only with --solver-cost.
      options.reportCost = true;
      options.jobs = jobs;
      options.memoryBallastMb = memoryBallastMb;
      options.slice = slice > 0   ? pia::verify::Options::Slice::On
                      : slice < 0 ? pia::verify::Options::Slice::Off
                                  : pia::verify::Options::Slice::Auto;
      options.cacheDir = proofCache;
      options.only = verifyOnly;
      options.checkVacuity = checkVacuity;
      // Which axioms each proof used is only reported by these, and kept
      // in proof cache entries for later runs to report (ADR 0036).
      options.trackAxioms =
          verifyStats || trustReport || checkVacuity || !proofCache.empty();
      if (module && codegen) {
        return compile(*module, mode, output, cg, allowUnproved, options,
                       verifyStats);
      } else if (module && verify) {
        pia::verify::Stats stats;
        if (mlir::failed(pia::verify::resolveOverloads(*module, options))) {
          std::cerr << "piac: internal error: cannot choose between "
                       "overloads\n";
          return 1;
        }
        std::vector<pia::verify::Outcome> outcomes =
            pia::verify::verifyModule(*module, options, &stats);
        if (verifyStats) {
          printStats(stats);
          printGoalAxioms(outcomes);
        }
        if (trustReport)
          printTrustReport(*module, stats, outcomes, trustWhy, std::cout);
        if (checkVacuity && stats.vacuityUnknown)
          std::cerr << "piac: note: --check-vacuity could not decide "
                    << stats.vacuityUnknown << " of " << stats.vacuityChecks
                    << " checked goals within its budget; they stay proved\n";
        if (!verifyOnly.empty() && stats.goals == 0) {
          std::cerr << "piac: error: --verify-only selects no goal\n";
          return 1;
        }
        bool failed =
            report(outcomes, mode == "--emit=mlir" ? std::cerr : std::cout,
                   solverCost, &stats, goalTimes);
        if (lints.on("costly_goal"))
          warnCostly(outcomes,
                     costlyGoal >= 0 ? static_cast<unsigned long long>(costlyGoal)
                                     : solverRlimit / 10ull,
                     solverRlimit);
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
