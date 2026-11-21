// The asynchronous Kernel over a Session (docs/repl.md, "The session API").

#include "repl/Kernel.h"

#include <chrono>

#include "gtest/gtest.h"

namespace pia::repl {
namespace {

using namespace std::chrono_literals;

TEST(Kernel, RunsJobsInOrderAndKeepsResults) {
  Kernel k;
  uint64_t a = k.submit("let sum (a : u8) (b : u8) : u16 = a + b");
  uint64_t b = k.submit("sum 2 3");
  EXPECT_EQ(a, 1u);
  EXPECT_EQ(b, 2u);
  Kernel::Status s = k.poll(b, 60s);
  ASSERT_EQ(s.state, Kernel::State::Done);
  ASSERT_TRUE(s.result);
  EXPECT_TRUE(s.result->ok);
  ASSERT_FALSE(s.result->events.empty());
  EXPECT_EQ(s.result->events.back().kind, Event::Kind::Value);
  EXPECT_EQ(s.result->events.back().value, "5");
  // The first job finished before the second started, and is still there.
  Kernel::Status first = k.poll(a);
  EXPECT_EQ(first.state, Kernel::State::Done);
  EXPECT_EQ(k.pending(), 0u);
}

TEST(Kernel, UnknownJobs) {
  Kernel k;
  EXPECT_EQ(k.poll(0).state, Kernel::State::Unknown);
  EXPECT_EQ(k.poll(7).state, Kernel::State::Unknown);
}

TEST(Kernel, PollWithoutWaiting) {
  Kernel k;
  uint64_t j = k.submit("let x : u8 = 1");
  Kernel::Status s = k.poll(j);
  EXPECT_NE(s.state, Kernel::State::Unknown);
  EXPECT_EQ(k.poll(j, 60s).state, Kernel::State::Done);
}

}  // namespace
}  // namespace pia::repl
