// pia-lsp's server: the Language Server Protocol over a byte stream
// (ADR 0021). Front-end features run on the request thread; proofs run on
// a worker thread when a ProofChecker is given.

#ifndef PIA_LSP_SERVER_H
#define PIA_LSP_SERVER_H

#include <iosfwd>
#include <optional>
#include <string>

#include "lsp/Json.h"
#include "lsp/Proofs.h"

namespace pia::lsp {

// Reads one message framed with a Content-Length header. Returns nullopt
// at end of input or on a malformed header.
std::optional<std::string> readMessage(std::istream &in);

// Writes one message with its Content-Length header and flushes.
void writeMessage(std::ostream &out, const std::string &body);

// "file:///a%20b/c.pia" -> "/a b/c.pia"; other URIs are returned as they are.
std::string uriToPath(const std::string &uri);

struct ServerOptions {
  ProofChecker checker; // empty in a build without MLIR
  std::string version = "0.1.0";
};

// Serves until `exit`. Returns the process exit status: 0 if `shutdown`
// came first, else 1.
int serve(std::istream &in, std::ostream &out, ServerOptions options);

} // namespace pia::lsp

#endif // PIA_LSP_SERVER_H
