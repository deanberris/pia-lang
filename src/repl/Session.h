// The REPL session: a persistent environment of verified definitions that
// grows one cell at a time, as in a Lisp REPL (ADR 0031, docs/repl.md).
//
// A cell is either Pia code or a `:command`. Code is parsed together with
// the environment, its metaprograms run, and the whole environment is
// lowered and verified again. The cell is committed only if every
// obligation is proved (or accepted with `:allow`), so the environment is
// always a program that verifies. Expressions in the cell are then compiled
// with the ORC JIT (through MLIR's ExecutionEngine) and run.
//
// The session is the core that every front end shares: `pia repl` in a
// terminal, `pia repl --json` for scripts and tools, the planned MCP server
// (`execute` and `poll`, through repl::Kernel) and the planned Jupyter
// kernel. Nothing in it prints: each cell returns a list of events, which
// the front end renders as text (render) or JSON (toJson).

#ifndef PIA_REPL_SESSION_H
#define PIA_REPL_SESSION_H

#include <memory>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include "lsp/Json.h"
#include "meta/Expand.h"

namespace pia::repl {

// Where an event points: line and column inside a cell's own text. Cell 0
// means no location.
struct Where {
  unsigned cell = 0;
  unsigned line = 0;
  unsigned column = 0;
};

struct Event {
  enum class Kind {
    Defined,   // a definition joined the environment: name, type
    Redefined, // one replaced an older definition: name, type
    Removed,   // :forget took one out: name
    Value,     // an expression or a constant was evaluated: name?, type, value
    Type,      // :type: text (what was asked about), type
    Proof,     // an obligation: name (function), status, text (claim), method
    Error,     // text, where?
    Info,      // text: command output, notes, warnings
    Task,      // a background task: name (its number), text (the
               // expression), type, status ("running" or "done"), value
  };
  Kind kind = Kind::Info;
  std::string name;
  std::string type;
  std::string value;
  std::string text;
  std::string status; // Proof: "proved", "failed", "unproved" or "allowed";
                      // Task: "running" or "done"
  std::string method; // Proof: "intervals", "smt", "presburger", or a reason
  std::vector<std::pair<std::string, std::string>> counterexample;
  Where where;
};

// One goal that took the solver a while, for ProofStats::costliest.
struct GoalCost {
  std::string function; // the definition it belongs to, if any
  std::string claim;
  std::string status;
  Where where;
  double ms = 0;
  unsigned long long cost = 0; // Z3's resource count
  bool mine = false; // the cell's own, not one the environment re-proved
};

// What proving a cell took. Each cell proves the whole environment again,
// so the counts cover the cell's own goals and the environment's.
struct ProofStats {
  bool verified = false; // false for commands and cells that never got to
                         // the verifier
  double cellMs = 0;     // the whole cell, from parse to printed value
  double verifyMs = 0;   // encoding and solving
  double solveMs = 0;    // wall clock, with goals solved in parallel
  unsigned threads = 0;  // solver threads
  double runMs = 0;      // compiling and running expressions
  unsigned goals = 0;    // every goal in the environment
  unsigned cellGoals = 0, cellIntervals = 0, cellSmt = 0;     // this cell's
  unsigned proved = 0, failed = 0, unproved = 0, allowed = 0; // every goal
  unsigned smt = 0;            // goals that needed the solver
  unsigned long long cost = 0; // Z3's resource count over every goal
  // The slowest solver goals, slowest first: up to three of the cell's own,
  // then up to three the environment re-proved.
  std::vector<GoalCost> costliest;
};

struct CellResult {
  unsigned cell = 0; // the cell's number, counting from 1
  bool ok = true;    // false when anything in the cell failed
  std::vector<Event> events;
  ProofStats stats;
};

struct Options {
  // Obligations accepted unproved, as `piac --allow-unproved`: a function
  // name, or a location "[cell]:line" or "[cell]:line:col".
  std::vector<std::string> allowUnproved;
  meta::Options meta;
  unsigned timeoutMs = 10000; // per obligation
  // How long a swap waits for running tasks to leave the definitions it
  // changes together (ADR 0031, "Live redefinition").
  unsigned quiesceMs = 2000;
  bool run = true; // false: verify, but never compile or run
};

class Session {
public:
  explicit Session(Options options = {});
  ~Session();
  Session(const Session &) = delete;
  Session &operator=(const Session &) = delete;

  // Runs one cell: code, or a command such as `:type e` (`:help` lists
  // them). Not thread safe: Kernel serialises calls from other threads.
  CellResult execute(std::string_view cell);

  // Empties the environment. Cell numbers keep counting.
  void reset();

  // The names the environment defines, in the order they were defined.
  std::vector<std::string> names() const;

  // Whether `text` is a complete cell, or needs more lines: it ends inside
  // a bracket, a comment, a string or a quote, or with a token that must be
  // followed by more (`=`, an operator, `then`, `in`, ...). Front ends use
  // it to read multi-line cells.
  static bool isComplete(std::string_view text);

private:
  struct Impl;
  std::unique_ptr<Impl> impl_;
};

// A cell's events as text, the way `pia repl` prints them.
std::string render(const CellResult &result);

// What a cell's proof took, in a few lines: time, goals by status and
// method, and the slowest goals. Empty when the cell proved nothing. The
// MCP server adds it to every result; `pia repl` does not print it, since
// times differ between runs and its output is checked by the docs' tests.
std::string renderStats(const ProofStats &stats);

// A cell's events as JSON, the way `pia repl --json` and the MCP server
// return them (docs/repl.md, "JSON output").
lsp::Json toJson(const CellResult &result);
lsp::Json toJson(const Event &event);

} // namespace pia::repl

#endif // PIA_REPL_SESSION_H
