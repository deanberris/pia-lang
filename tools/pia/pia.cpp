// pia: the Pia tool.
//
//   pia repl [options] [file.pia ...]   the REPL
//   pia mcp [options]                   an MCP server over a REPL session,
//                                       with the tools execute and poll
//
// Options:
//   --json                 read JSON requests and write JSON results, one
//                          per line (both --input=json and --output=json)
//   --input=text|json      how cells arrive on standard input
//   --output=text|json     how results are written
//   --no-run               verify cells, but never compile or run them
//   --allow-unproved=SPEC  accept unproved obligations in function SPEC, or
//                          at SPEC = [cell]:line[:col] (also :allow)
//   --meta-cycles=N        cap metaprogram expansion at N passes
//   --timeout-ms=N         the solver's time limit per obligation
//
// Each file is loaded as one cell first. On a terminal, `pia repl` then
// reads cells with a line editor; otherwise it reads them from standard
// input until it ends. docs/repl.md describes cells, commands and the JSON
// protocol.
//
// Exit status: 0, or 1 when any cell read from a pipe or a file failed, or
// 2 on a usage error.

#include <cstdlib>
#include <iostream>
#include <optional>
#include <string>
#include <vector>

#include "lsp/Json.h"
#include "repl/LineEditor.h"
#include "repl/Mcp.h"
#include "repl/Session.h"

namespace {

using pia::repl::CellResult;
using pia::repl::Session;

int usage() {
  std::cerr << "usage: pia mcp [--no-run] [--allow-unproved=<spec>]... "
               "[--meta-cycles=N] [--timeout-ms=N]\n"
               "       pia repl [--json] [--input=text|json] "
               "[--output=text|json] [--no-run]\n"
               "                [--allow-unproved=<spec>]... "
               "[--meta-cycles=N] [--timeout-ms=N] [file.pia ...]\n";
  return 2;
}

struct Repl {
  Session &session;
  bool jsonOut = false;
  bool failed = false;

  // Runs one cell and prints its result. Returns false after :quit.
  bool run(const std::string &cell, const pia::lsp::Json *id = nullptr) {
    CellResult r = session.execute(cell);
    failed |= !r.ok;
    if (jsonOut) {
      pia::lsp::Json j = pia::repl::toJson(r);
      if (id) j["id"] = *id;
      std::cout << j.dump() << "\n";
    } else {
      std::cout << pia::repl::render(r);
    }
    std::cout.flush();
    std::string t = cell;
    t.erase(0, t.find_first_not_of(" \t\r\n"));
    return !(t.rfind(":quit", 0) == 0 || t == ":q" || t.rfind(":q ", 0) == 0);
  }
};

// Whether `line` can start a new cell: it starts at column 1, and is not
// the `=` that begins a definition's body after its contracts.
bool startsAtColumnOne(const std::string &line) {
  return !line.empty() && line[0] != ' ' && line[0] != '\t' && line[0] != '\r' &&
         line[0] != '=';
}

// Cells from a pipe: a cell ends where the next line starts at column 1,
// once what came before is complete (Session::isComplete).
void readPipe(Repl &repl) {
  std::string cell, line;
  auto flush = [&] {
    bool go = true;
    if (cell.find_first_not_of(" \t\r\n") != std::string::npos) go = repl.run(cell);
    cell.clear();
    return go;
  };
  while (std::getline(std::cin, line)) {
    if (startsAtColumnOne(line) && !cell.empty() && Session::isComplete(cell))
      if (!flush()) return;
    cell += line;
    cell += "\n";
  }
  flush();
}

// JSON requests, one per line: {"code": "...", "id": ...}.
void readJson(Repl &repl) {
  std::string line;
  while (std::getline(std::cin, line)) {
    if (line.find_first_not_of(" \t\r") == std::string::npos) continue;
    std::optional<pia::lsp::Json> req = pia::lsp::Json::parse(line);
    if (!req || !req->isObject() || !(*req)["code"].isString()) {
      pia::lsp::Json err;
      err["ok"] = false;
      pia::lsp::Json e;
      e["kind"] = "error";
      e["text"] = "expected a JSON object with a \"code\" string";
      err["events"] = pia::lsp::Json::Array{e};
      std::cout << err.dump() << "\n";
      std::cout.flush();
      repl.failed = true;
      continue;
    }
    const pia::lsp::Json &id = (*req)["id"];
    if (!repl.run((*req)["code"].asString(), id.isNull() ? nullptr : &id)) return;
  }
}

// The terminal: a line editor, with a continuation prompt while a cell is
// incomplete. An empty line ends a cell early.
void readTerminal(Repl &repl) {
  std::string history;
  if (const char *home = std::getenv("HOME")) history = std::string(home) + "/.pia_history";
  pia::repl::LineEditor editor(history);
  std::cout << "Pia REPL. Definitions are proved before they join the "
               "environment. :help lists the commands.\n";
  std::string cell;
  for (;;) {
    std::optional<std::string> line = editor.read(cell.empty() ? "pia> " : "...> ");
    if (!line) break;
    if (editor.interrupted()) {
      cell.clear();
      continue;
    }
    bool blank = line->find_first_not_of(" \t") == std::string::npos;
    if (blank && cell.empty()) continue;
    if (!blank) cell += *line + "\n";
    if (blank || Session::isComplete(cell)) {
      std::string c = cell;
      cell.clear();
      while (!c.empty() && c.back() == '\n') c.pop_back();
      editor.remember(c);
      if (!repl.run(c)) break;
    }
  }
}

}  // namespace

int main(int argc, char **argv) {
  if (argc < 2) return usage();
  std::string command = argv[1];
  if (command != "repl" && command != "mcp") return usage();
  pia::repl::Options options;
  bool jsonIn = false, jsonOut = false;
  std::vector<std::string> files;
  for (int i = 2; i < argc; ++i) {
    std::string arg = argv[i];
    auto number = [&](size_t prefix, unsigned &out) {
      char *end = nullptr;
      long n = std::strtol(arg.c_str() + prefix, &end, 10);
      if (*end != '\0' || n < 0 || end == arg.c_str() + prefix) return false;
      out = static_cast<unsigned>(n);
      return true;
    };
    if (arg == "--json") {
      jsonIn = jsonOut = true;
    } else if (arg == "--input=json" || arg == "--input=text") {
      jsonIn = arg == "--input=json";
    } else if (arg == "--output=json" || arg == "--output=text") {
      jsonOut = arg == "--output=json";
    } else if (arg == "--no-run") {
      options.run = false;
    } else if (arg.rfind("--allow-unproved=", 0) == 0 && arg.size() > 17) {
      options.allowUnproved.push_back(arg.substr(17));
    } else if (arg.rfind("--meta-cycles=", 0) == 0) {
      if (!number(14, options.meta.maxCycles)) return usage();
    } else if (arg.rfind("--timeout-ms=", 0) == 0) {
      if (!number(13, options.timeoutMs)) return usage();
    } else if (!arg.empty() && arg[0] == '-') {
      return usage();
    } else {
      files.push_back(arg);
    }
  }

  if (command == "mcp") {
    if (jsonIn || jsonOut || !files.empty()) return usage();
    pia::repl::McpServer server(options);
    server.serve(std::cin, std::cout);
    return 0;
  }

  Session session(options);
  Repl repl{session, jsonOut};
  for (const std::string &f : files)
    if (!repl.run(":load " + f)) return repl.failed ? 1 : 0;
  if (jsonIn)
    readJson(repl);
  else if (pia::repl::LineEditor::isTerminal()) {
    readTerminal(repl);
    return 0;  // failed cells are part of working interactively
  } else
    readPipe(repl);
  return repl.failed ? 1 : 0;
}
