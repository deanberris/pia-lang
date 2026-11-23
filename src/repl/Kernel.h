// An asynchronous front for a Session: cells are submitted as jobs that run
// one at a time on a worker thread, and their results are polled. This is
// the shape the MCP server's `execute` and `poll` tools and the planned
// Jupyter kernel need (docs/repl.md, "The session API").

#ifndef PIA_REPL_KERNEL_H
#define PIA_REPL_KERNEL_H

#include <chrono>
#include <condition_variable>
#include <cstdint>
#include <deque>
#include <map>
#include <mutex>
#include <optional>
#include <string>
#include <thread>

#include "repl/Session.h"

namespace pia::repl {

class Kernel {
public:
  enum class State { Queued, Running, Done, Unknown };

  struct Status {
    uint64_t job = 0;
    State state = State::Unknown;
    std::optional<CellResult> result; // set once the job is Done
  };

  explicit Kernel(Options options = {});
  ~Kernel(); // finishes the running job, drops queued ones
  Kernel(const Kernel &) = delete;
  Kernel &operator=(const Kernel &) = delete;

  // Queues a cell and returns its job number, counting from 1.
  uint64_t submit(std::string cell);

  // The job's state, waiting up to `wait` for it to finish. A finished
  // job's result is kept for the life of the kernel, so polling it again
  // returns the same result.
  Status poll(uint64_t job, std::chrono::milliseconds wait = {});

  // Jobs that are queued or running.
  size_t pending() const;

private:
  void work();

  Session session_;
  mutable std::mutex mutex_;
  std::condition_variable changed_;
  std::deque<std::pair<uint64_t, std::string>> queue_;
  std::map<uint64_t, CellResult> done_;
  uint64_t next_ = 0;
  uint64_t running_ = 0;
  bool stop_ = false;
  std::thread worker_;
};

const char *stateName(Kernel::State state);

} // namespace pia::repl

#endif // PIA_REPL_KERNEL_H
