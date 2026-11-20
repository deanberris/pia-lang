// piac: the Pia compiler driver. M2 supports parsing only.
//
//   piac --dump-ast file.pia        print the syntax tree
//   piac --dump-tokens file.pia     print the token stream
//   piac --check file.pia           parse and report errors only
//   piac --fragment=contracts ...   parse a file of contract clauses
//
// Exit status: 0 on success, 1 on a syntax error, 2 on a usage error.

#include <fstream>
#include <iostream>
#include <sstream>
#include <string>

#include "syntax/Lexer.h"
#include "syntax/Parser.h"
#include "syntax/Syntax.h"

namespace {

int usage() {
  std::cerr << "usage: piac (--dump-ast | --dump-tokens | --check) "
               "[--fragment=contracts] <file.pia>\n";
  return 2;
}

}  // namespace

int main(int argc, char **argv) {
  std::string mode, file;
  bool contracts = false;
  for (int i = 1; i < argc; ++i) {
    std::string arg = argv[i];
    if (arg == "--dump-ast" || arg == "--dump-tokens" || arg == "--check")
      mode = arg;
    else if (arg == "--fragment=contracts")
      contracts = true;
    else if (!arg.empty() && arg[0] == '-')
      return usage();
    else
      file = arg;
  }
  if (mode.empty() || file.empty()) return usage();

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
  }
  if (diags.hasErrors()) {
    diags.print(std::cerr, file, source);
    return 1;
  }
  return 0;
}
