#include "repl/Kernel.h"

namespace pia::repl {

Kernel::Kernel(Options options)
    : session_(std::move(options)), worker_([this] { work(); }) {}

Kernel::~Kernel() {
  {
    std::lock_guard<std::mutex> lock(mutex_);
    stop_ = true;
    queue_.clear();
  }
  changed_.notify_all();
  worker_.join();
}

uint64_t Kernel::submit(std::string cell) {
  uint64_t job;
  {
    std::lock_guard<std::mutex> lock(mutex_);
    job = ++next_;
    queue_.emplace_back(job, std::move(cell));
  }
  changed_.notify_all();
  return job;
}

Kernel::Status Kernel::poll(uint64_t job, std::chrono::milliseconds wait) {
  std::unique_lock<std::mutex> lock(mutex_);
  Status s;
  s.job = job;
  if (job == 0 || job > next_) return s;
  changed_.wait_for(lock, wait, [&] { return done_.count(job) || stop_; });
  auto it = done_.find(job);
  if (it != done_.end()) {
    s.state = State::Done;
    s.result = it->second;
  } else if (running_ == job) {
    s.state = State::Running;
  } else {
    s.state = State::Queued;
  }
  return s;
}

size_t Kernel::pending() const {
  std::lock_guard<std::mutex> lock(mutex_);
  return queue_.size() + (running_ ? 1 : 0);
}

void Kernel::work() {
  for (;;) {
    std::pair<uint64_t, std::string> job;
    {
      std::unique_lock<std::mutex> lock(mutex_);
      changed_.wait(lock, [&] { return stop_ || !queue_.empty(); });
      if (stop_) return;
      job = std::move(queue_.front());
      queue_.pop_front();
      running_ = job.first;
    }
    CellResult r = session_.execute(job.second);
    {
      std::lock_guard<std::mutex> lock(mutex_);
      done_.emplace(job.first, std::move(r));
      running_ = 0;
    }
    changed_.notify_all();
  }
}

const char *stateName(Kernel::State state) {
  switch (state) {
    case Kernel::State::Queued: return "queued";
    case Kernel::State::Running: return "running";
    case Kernel::State::Done: return "done";
    case Kernel::State::Unknown: return "unknown";
  }
  return "unknown";
}

}  // namespace pia::repl
