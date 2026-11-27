#include "migrate/Migrate.h"

#include <string>

#include "syntax/Diagnostics.h"
#include "syntax/Parser.h"
#include "gtest/gtest.h"

using namespace pia;

namespace {

syntax::NodePtr parse(const std::string &source) {
  syntax::Diagnostics diags;
  syntax::NodePtr tree = syntax::parseProgram(source, diags);
  EXPECT_FALSE(diags.hasErrors());
  return tree;
}

// A rule made for the test, for a deprecated form with a safe rewrite:
// each `old_name` becomes `new_name`.
void renameOld(const migrate::Rule &rule, const syntax::Node &,
               std::string_view source, std::vector<syntax::Lint> &out) {
  for (size_t at = source.find("old_name"); at != std::string_view::npos;
       at = source.find("old_name", at + 1)) {
    syntax::Lint l;
    l.name = rule.id;
    l.loc.offset = uint32_t(at);
    l.end = uint32_t(at + 8);
    l.message = "'old_name' is now 'new_name'";
    l.edits.push_back({uint32_t(at), uint32_t(at + 8), "new_name"});
    out.push_back(std::move(l));
  }
}

const std::vector<migrate::Rule> &testRules() {
  static const std::vector<migrate::Rule> all = {
      {"rename-old", "0.0.0+700", "old_name is new_name", "a test",
       /*inBuilds=*/true, renameOld},
  };
  return all;
}

TEST(Migrate, RewritesAndIsIdempotent) {
  std::string source = "let old_name = 1\nlet b = old_name + 2\n";
  syntax::NodePtr tree = parse(source);
  std::vector<syntax::Lint> found =
      migrate::find(*tree, source, "", false, testRules());
  ASSERT_EQ(found.size(), 2u);
  size_t applied = 0;
  std::string out = migrate::apply(source, found, applied);
  EXPECT_EQ(applied, 2u);
  EXPECT_EQ(out, "let new_name = 1\nlet b = new_name + 2\n");
  syntax::NodePtr again = parse(out);
  EXPECT_TRUE(migrate::find(*again, out, "", false, testRules()).empty());
}

TEST(Migrate, FromSkipsOlderRules) {
  std::string source = "let old_name = 1\n";
  syntax::NodePtr tree = parse(source);
  EXPECT_EQ(
      migrate::find(*tree, source, "0.0.0+699.abc", false, testRules()).size(),
      1u);
  EXPECT_TRUE(migrate::find(*tree, source, "0.0.0+700.abc", false, testRules())
                  .empty());
}

TEST(Migrate, OverlappingEditsWaitForTheNextPass) {
  std::vector<syntax::Lint> lints(2);
  lints[0].edits.push_back({0, 4, "AB"});
  lints[1].edits.push_back({2, 6, "CD"});
  size_t applied = 0;
  EXPECT_EQ(migrate::apply("0123456789", lints, applied), "AB456789");
  EXPECT_EQ(applied, 1u);
}

TEST(Migrate, SuggestionsAreNotApplied) {
  std::vector<syntax::Lint> lints(1);
  lints[0].edits.push_back({0, 4, "AB"});
  lints[0].preferred = false;
  size_t applied = 0;
  EXPECT_EQ(migrate::apply("0123", lints, applied), "0123");
  EXPECT_EQ(applied, 0u);
}

TEST(TypeMakesDistinct, FindsOnlyTheOldAliasForm) {
  std::string source = "let blk = type int{0..63}\n"
                       "let point = type { x : int; y : int }\n"
                       "let length = type u32\n"
                       "let byte = u8\n";
  syntax::NodePtr tree = parse(source);
  std::vector<syntax::Lint> found = migrate::find(*tree, source, "", false);
  ASSERT_EQ(found.size(), 2u);
  EXPECT_EQ(found[0].name, "type-makes-distinct");
  EXPECT_EQ(found[0].loc.line, 1u);
  EXPECT_EQ(found[1].loc.line, 3u);
  EXPECT_FALSE(found[0].preferred);
  // Its quick fix keeps the old meaning.
  size_t applied = 0;
  std::vector<syntax::Lint> fix = {found[0]};
  fix[0].preferred = true;
  EXPECT_EQ(migrate::apply(source, fix, applied).substr(0, 23),
            "let blk = int{0..63}\nle");
  // A build never runs it, and neither does a migration from after it.
  EXPECT_TRUE(migrate::find(*tree, source, "", true).empty());
  EXPECT_TRUE(migrate::find(*tree, source, "0.0.0+634", false).empty());
}

} // namespace
