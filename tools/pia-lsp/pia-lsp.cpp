// pia-lsp: the Pia language server (ADR 0021). It speaks the Language
// Server Protocol on stdin and stdout; editors start it as a subprocess.
//
//   pia-lsp                       serve over stdio
//   pia-lsp --timeout-ms=<n>      per-goal solver timeout (default 10000)
//   pia-lsp --version
//
// Built with -DPIA_NO_MLIR it has only the front-end features: syntax
// diagnostics, symbols, hover, definitions and completion.

#include <cstdlib>
#include <iostream>
#include <string>

#include "lsp/Server.h"

int main(int argc, char **argv) {
  unsigned timeoutMs = 10000;
  pia::lsp::ServerOptions options;
  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg == "--version") {
      std::cout << "pia-lsp " << options.version << "\n";
      return 0;
    } else if (arg.rfind("--timeout-ms=", 0) == 0) {
      timeoutMs = static_cast<unsigned>(std::strtoul(arg.c_str() + 13, nullptr, 10));
    } else if (arg == "--stdio") {
      // what VS Code passes; stdio is the only transport
    } else {
      std::cerr << "usage: pia-lsp [--stdio] [--timeout-ms=<n>] [--version]\n";
      return 2;
    }
  }
#ifndef PIA_NO_MLIR
  options.checker = [timeoutMs](std::string_view source, const std::string &path) {
    return pia::lsp::checkProofs(source, path, timeoutMs);
  };
#else
  (void)timeoutMs;
#endif
  std::ios::sync_with_stdio(false);
  return pia::lsp::serve(std::cin, std::cout, std::move(options));
}
