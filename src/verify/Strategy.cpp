#include "verify/Strategy.h"

#include <array>
#include <cctype>
#include <stdexcept>
#include <vector>

#include "llvm/ADT/StringRef.h"

namespace pia::verify {

namespace {

// A strategy, `nlsat` or `(then simplify smt)`, read as Z3 tactics.
class StrategyReader {
 public:
  StrategyReader(z3::context &ctx, llvm::StringRef text)
      : ctx_(ctx), text_(text) {}

  z3::tactic read() {
    z3::tactic t = tactic();
    skip();
    if (pos_ < text_.size()) fail("unexpected '" + text_.substr(pos_).str() + "'");
    return t;
  }

 private:
  [[noreturn]] void fail(const std::string &why) {
    throw std::runtime_error(why);
  }

  void skip() {
    while (pos_ < text_.size() && std::isspace(static_cast<unsigned char>(text_[pos_])))
      ++pos_;
  }

  std::string atom() {
    skip();
    size_t start = pos_;
    while (pos_ < text_.size() && text_[pos_] != '(' && text_[pos_] != ')' &&
           !std::isspace(static_cast<unsigned char>(text_[pos_])))
      ++pos_;
    if (start == pos_ && pos_ >= text_.size())
      fail("the strategy ends before a ')' closes it");
    if (start == pos_) fail("expected a tactic");
    return text_.substr(start, pos_ - start).str();
  }

  bool peek(char c) {
    skip();
    return pos_ < text_.size() && text_[pos_] == c;
  }

  void expect(char c) {
    if (!peek(c)) fail(std::string("expected '") + c + "'");
    ++pos_;
  }

  unsigned number() {
    std::string a = atom();
    unsigned n = 0;
    if (llvm::StringRef(a).getAsInteger(10, n)) fail("expected a number, found '" + a + "'");
    return n;
  }

  z3::tactic named(const std::string &name) {
    try {
      return z3::tactic(ctx_, name.c_str());
    } catch (const z3::exception &) {
      fail("Z3 has no tactic '" + name + "'");
    }
  }

  z3::tactic tactic() {
    if (!peek('(')) return named(atom());
    ++pos_;
    std::string head = atom();
    z3::tactic out(ctx_, "skip");
    if (head == "then" || head == "and-then" || head == "or-else" ||
        head == "par-or" || head == "par-then") {
      std::vector<z3::tactic> ts;
      while (!peek(')')) ts.push_back(tactic());
      if (ts.size() < 2) fail("'" + head + "' takes two or more tactics");
      out = ts[0];
      for (size_t i = 1; i < ts.size(); ++i)
        out = head == "or-else"    ? (out | ts[i])
              : head == "par-or"   ? z3::par_or(2, std::array{out, ts[i]}.data())
              : head == "par-then" ? z3::par_and_then(out, ts[i])
                                   : (out & ts[i]);
    } else if (head == "repeat") {
      z3::tactic t = tactic();
      out = peek(')') ? z3::repeat(t) : z3::repeat(t, number());
    } else if (head == "try-for") {
      z3::tactic t = tactic();
      out = z3::try_for(t, number());
    } else if (head == "using-params" || head == "!") {
      z3::tactic t = tactic();
      z3::params ps(ctx_);
      while (!peek(')')) {
        std::string key = atom();
        if (key.empty() || key[0] != ':') fail("expected a parameter such as ':arith.solver'");
        std::string value = atom();
        unsigned n = 0;
        if (value == "true" || value == "false")
          ps.set(key.substr(1).c_str(), value == "true");
        else if (!llvm::StringRef(value).getAsInteger(10, n))
          ps.set(key.substr(1).c_str(), n);
        else
          ps.set(key.substr(1).c_str(), ctx_.str_symbol(value.c_str()));
      }
      out = z3::with(t, ps);
    } else {
      fail("'" + head + "' is not a tactic combinator; use then, or-else, "
           "par-or, par-then, repeat, try-for or using-params");
    }
    expect(')');
    return out;
  }

  z3::context &ctx_;
  llvm::StringRef text_;
  size_t pos_ = 0;
};

}  // namespace

z3::solver solverFor(z3::context &ctx, const std::string &strategy) {
  if (strategy.empty()) return z3::solver(ctx);
  return StrategyReader(ctx, strategy).read().mk_solver();
}

std::optional<std::string> checkStrategy(const std::string &strategy) {
  z3::context ctx;
  try {
    StrategyReader(ctx, strategy).read();
  } catch (const std::runtime_error &e) {
    return std::string(e.what());
  } catch (const z3::exception &e) {
    return std::string(e.msg());
  }
  return std::nullopt;
}

}  // namespace pia::verify
