// Verifier v0 (milestone M5): proves the obligations of a lowered module.
// docs/verifier.md describes the obligations, the encoding and its limits.

#ifndef PIA_VERIFY_VERIFIER_H
#define PIA_VERIFY_VERIFIER_H

#include <string>
#include <vector>

#include "dialect/ContractDialect.h"
#include "mlir/IR/BuiltinOps.h"
#include "mlir/IR/Location.h"

namespace pia::verify {

enum class Status { Proved, Failed, Skipped };

struct ModelValue {
  std::string name;   // a parameter name, or a label such as "result"
  std::string value;  // decimal, or true/false
};

struct Outcome {
  Status status = Status::Skipped;
  contract::ObligationKind kind = contract::ObligationKind::assert_;
  std::string where;   // "file:line:col"
  std::string function;  // the enclosing function's symbol name
  std::string claim;   // what must hold, e.g. "'+' does not overflow u8"
  std::string method;  // "intervals" or "smt" when proved, else the reason
  std::vector<ModelValue> counterexample;
  unsigned long long cost = 0;  // Z3's resource count, with reportCost
};

struct Options {
  unsigned timeoutMs = 10000;  // per obligation, wall clock
  // Z3's deterministic resource limit per obligation; 0 for none. Unlike
  // the timeout, it does not depend on how busy the machine is.
  unsigned rlimit = 0;
  bool reportCost = false;     // record each query's resource use
  bool dumpSmt = false;        // print each query's SMT-LIB to stderr

  // Solver threads; 0 for one per core. Each SMT goal is solved in its own
  // Z3 context, and outcomes keep the walk order, so the report does not
  // depend on the number of threads (ADR 0032).
  unsigned jobs = 0;
  // Goal slicing: drop the assertions that share no symbol with the goal,
  // directly or transitively, before solving. A sliced query that is not
  // unsat is solved again in full, so slicing changes only how fast a goal
  // is proved, never whether it is. Auto, the default, slices only in a
  // function with a buffer of records ({pia.record_buffers}), and only
  // when the slice drops a declaration the goal cannot reach, such as the
  // field buffers of fields the goal never mentions. Elsewhere slicing
  // costs more than it saves on the benchmark (ADR 0032), so Auto solves
  // the full query. On (--slice) slices whenever the slice is smaller;
  // Off (--no-slice) always solves the full query.
  enum class Slice { Auto, On, Off };
  Slice slice = Slice::Auto;
  // Proved goals are recorded here, one file per goal hash; empty for no
  // cache. The hash covers the whole query, the solver version and the
  // rlimit, so a hit is the proof the solver would find again.
  std::string cacheDir;
  // Prove only the goals these specs select: a function name, a module
  // (its file name, such as "edges.pia"), or a location "file:line" or
  // "file:line:col". Empty selects every goal. Unselected goals are left out
  // of the outcomes; earlier goals are still assumed, as in a full run.
  std::vector<std::string> only;
};

// What one verifyModule call did, for --verify-stats and the build-time
// benchmark (tools/bench).
struct Stats {
  unsigned goals = 0;        // selected goals
  unsigned unselected = 0;   // goals --verify-only left out
  unsigned intervals = 0;    // proved without the solver
  unsigned skipped = 0;
  unsigned solved = 0;       // queries sent to Z3
  unsigned cached = 0;       // goals the proof cache answered
  unsigned sliced = 0;       // queries slicing made smaller
  unsigned unsliced = 0;     // sliced queries solved again in full
  unsigned threads = 0;
  unsigned long long cost = 0;  // Z3 resource count over every query
  double encodeMs = 0, solveMs = 0;
  // Where the selected goals came from (ADR 0037). Type goals are raised by
  // operations on typed values: overflow and narrowing into a range type,
  // bounds, divisors, shifts, match exhaustiveness and out parameters.
  // Contract goals are written ones: requires at calls, ensures, loop
  // invariants, decreases, assertions and concept laws. `*Smt` counts the
  // ones that needed the solver, and `*Cost` their resource count, when
  // Options::reportCost is set.
  unsigned typeGoals = 0, typeSmt = 0;
  unsigned contractGoals = 0, contractSmt = 0;
  unsigned long long typeCost = 0, contractCost = 0;
};

// Whether a goal of this kind is written in a contract, rather than raised
// by the types of the values an operation uses.
bool isContractGoal(contract::ObligationKind kind);

// Whether `--verify-only=spec` selects a goal at `where` in `function`.
bool selects(const std::string &spec, const std::string &where,
             const std::string &function);

// Checks every function in `module`, in order, and marks each op whose
// obligations all hold with `pia.proved = "intervals"` or `"smt"`. It first
// replaces record values with their fields (transforms/ScalarizeRecords.h),
// so the module afterwards has no records.
//
// Goals are encoded one at a time, then solved on `options.jobs` threads.
std::vector<Outcome> verifyModule(mlir::ModuleOp module,
                                  const Options &options = {},
                                  Stats *stats = nullptr);

// "file:line:col" for the innermost file location in `loc`.
std::string formatLoc(mlir::Location loc);

}  // namespace pia::verify

#endif  // PIA_VERIFY_VERIFIER_H
