#include "cert/Advisory.h"

#include <string>

#include "gtest/gtest.h"

using namespace pia::cert;

namespace {

// A certificate from piac `prover`, listing `engines` when given.
Certificate proved(std::string prover,
                   std::optional<std::vector<std::string>> engines = {}) {
  Certificate c;
  c.module = "Image.Pixels";
  c.abi = kAbiVersion;
  c.target = "arm64-apple-macos";
  c.prover = std::move(prover);
  c.solvers.push_back({"z3", "4.15.1"});
  c.engines = std::move(engines);
  return c;
}

Advisory parse(const std::string &text) {
  std::string error;
  std::optional<Advisory> a = parseAdvisory(text, error);
  EXPECT_TRUE(a) << error;
  return a.value_or(Advisory{});
}

// An advisory against a fake engine, so no real certificate matches it.
const char *kFake = R"(# A test advisory.
id = "PIA-2099-0001"
summary = "The fake engine proves anything"
piac = { introduced = "0.0.0+100", fixed = "0.1.0+200" }
engines = ["fake", "intervals"]
solver = {}
lean = []
severity = "unsound"
fixed_by = "https://example.invalid/fix"
)";

TEST(Advisory, Parses) {
  Advisory a = parse(kFake);
  EXPECT_EQ(a.id, "PIA-2099-0001");
  EXPECT_EQ(a.summary, "The fake engine proves anything");
  ASSERT_TRUE(a.piac);
  EXPECT_EQ(a.piac->introduced, "0.0.0+100");
  EXPECT_EQ(a.piac->fixed, "0.1.0+200");
  EXPECT_EQ(a.engines, (std::vector<std::string>{"fake", "intervals"}));
  EXPECT_TRUE(a.solvers.empty());
  EXPECT_EQ(a.severity, "unsound");
  EXPECT_EQ(a.fixedBy, "https://example.invalid/fix");
}

TEST(Advisory, ParsesSolverRanges) {
  Advisory a = parse(R"(id = "PIA-2099-0002"
summary = "z3 bug"
solver = { z3 = { introduced = "4.15.0", fixed = "4.15.2" } }
severity = "unsound"
)");
  ASSERT_EQ(a.solvers.size(), 1u);
  EXPECT_EQ(a.solvers[0].first, "z3");
  EXPECT_EQ(a.solvers[0].second.fixed, "4.15.2");
  EXPECT_TRUE(matches(proved("dev"), a));
  Certificate fixed = proved("dev");
  fixed.solvers[0].version = "4.15.2";
  EXPECT_FALSE(matches(fixed, a));
}

TEST(Advisory, RefusesMalformedFiles) {
  std::string error;
  EXPECT_FALSE(parseAdvisory("id = \"PIA-1\"\nsummary = \"x\"\n"
                             "severity = \"unsound\"\n",
                             error));
  EXPECT_NE(error.find("names no piac range"), std::string::npos) << error;
  EXPECT_FALSE(parseAdvisory("id = \"X-1\"\n", error));
  EXPECT_FALSE(parseAdvisory("colour = \"red\"\n", error));
  EXPECT_NE(error.find("unknown key"), std::string::npos) << error;
  EXPECT_FALSE(parseAdvisory("id = \"PIA-1\" junk\n", error));
  EXPECT_FALSE(parseAdvisory("id = \"PIA-1\nsummary = \"x\"\n", error));
}

TEST(Advisory, OrdersVersions) {
  EXPECT_LT(compareVersions("0.0.0+99.abc", "0.0.0+100.def"), 0);
  // The commit count orders builds on main across releases.
  EXPECT_LT(compareVersions("0.0.0+150.abc", "0.1.0+200.def"), 0);
  EXPECT_EQ(compareVersions("0.1.0+200.abc", "0.1.0+200"), 0);
  EXPECT_LT(compareVersions("0.1.0", "0.1.0+3.abc"), 0);
  EXPECT_LT(compareVersions("4.9.1", "4.15.0"), 0);
  EXPECT_EQ(compareVersions("4.15", "4.15.0"), 0);
}

TEST(Advisory, MatchesItsRangeAndEngines) {
  Advisory a = parse(kFake);
  EXPECT_TRUE(matches(proved("0.0.0+150.9f3c", {{"z3", "fake"}}), a));
  // The fixed version and those before the range do not match.
  EXPECT_FALSE(matches(proved("0.1.0+200.9f3c", {{"fake"}}), a));
  EXPECT_FALSE(matches(proved("0.0.0+99.9f3c", {{"fake"}}), a));
  // Engines narrow the range...
  EXPECT_FALSE(matches(proved("0.0.0+150.9f3c", {{"z3"}}), a));
  // ...but a certificate that does not list them may have used any.
  std::optional<std::string> why = matches(proved("0.0.0+150.9f3c"), a);
  ASSERT_TRUE(why);
  EXPECT_NE(why->find("does not say"), std::string::npos) << *why;
  // No range covers an unstamped piac.
  EXPECT_FALSE(matches(proved("dev", {{"fake"}}), a));
}

TEST(Advisory, IncompleteNeverRevokes) {
  Advisory a = parse(kFake);
  a.severity = "incomplete";
  EXPECT_FALSE(matches(proved("0.0.0+150.9f3c", {{"fake"}}), a));
}

TEST(Advisory, UnfixedRangeHasNoEnd) {
  Advisory a = parse(kFake);
  a.piac->fixed.clear();
  a.engines.clear();
  EXPECT_TRUE(matches(proved("9.0.0+99999.9f3c"), a));
}

TEST(Advisory, RevokesAToolchain) {
  std::vector<Advisory> all = {parse(kFake), parse(R"(id = "PIA-2099-0002"
summary = "z3 bug"
solver = { z3 = { introduced = "4.15.0", fixed = "4.15.2" } }
severity = "unsound"
)")};
  // A toolchain lists no engines, so the engine-narrowed advisory counts.
  std::vector<const Advisory *> r = revoking(proved("0.0.0+150.9f3c"), all);
  ASSERT_EQ(r.size(), 2u);
  EXPECT_EQ(r[0]->id, "PIA-2099-0001");
  // With the solver alone, only the solver advisory is left.
  Certificate solverOnly = proved("");
  r = revoking(solverOnly, all);
  ASSERT_EQ(r.size(), 1u);
  EXPECT_EQ(r[0]->id, "PIA-2099-0002");
  solverOnly.solvers[0].version = "4.15.2";
  EXPECT_TRUE(revoking(solverOnly, all).empty());
}

TEST(Advisory, BuiltinsParse) {
  // builtinAdvisories() stops the program on a malformed file, so this
  // proves every file in security/advisories reads.
  std::vector<Advisory> all = builtinAdvisories();
  ASSERT_FALSE(all.empty());
  EXPECT_EQ(all.front().id, "PIA-2026-0001");
}

TEST(Certificate, EnginesRoundTrip) {
  Certificate c = proved("dev", {{"intervals", "z3"}});
  std::string error;
  std::optional<Certificate> d = decode(encode(c), error);
  ASSERT_TRUE(d) << error;
  EXPECT_EQ(d->engines, c.engines);
  c.engines.emplace();
  d = decode(encode(c), error);
  ASSERT_TRUE(d) << error;
  ASSERT_TRUE(d->engines);
  EXPECT_TRUE(d->engines->empty());
  c.engines.reset();
  d = decode(encode(c), error);
  ASSERT_TRUE(d) << error;
  EXPECT_FALSE(d->engines);
}

} // namespace
