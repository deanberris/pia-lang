// An MCP server over a REPL Kernel, with two tools in the style of Code
// Mode (docs/repl.md, "MCP server"):
//
//   execute {code, wait_ms?}  run a cell in the persistent session; returns
//                             its result, or a job number if it is still
//                             running after wait_ms
//   poll {job, wait_ms?}      the state and, once done, the result of a job
//
// It speaks JSON-RPC 2.0 over newline-delimited stdio, as MCP's stdio
// transport does.
//
// It teaches the language through its instructions, the pia://guide/
// resources and hints on failed cells (repl/Guide.h).

#ifndef PIA_REPL_MCP_H
#define PIA_REPL_MCP_H

#include <istream>
#include <ostream>

#include "lsp/Json.h"
#include "repl/Kernel.h"

namespace pia::repl {

class McpServer {
public:
  explicit McpServer(Options options = {}) : kernel_(std::move(options)) {}

  // Answers one JSON-RPC message. Returns null for a notification.
  lsp::Json handle(const lsp::Json &message);

  // Reads messages until the input ends.
  void serve(std::istream &in, std::ostream &out);

private:
  lsp::Json callTool(const std::string &name, const lsp::Json &args);
  lsp::Json jobResult(const Kernel::Status &s, bool json);

  Kernel kernel_;
};

} // namespace pia::repl

#endif // PIA_REPL_MCP_H
