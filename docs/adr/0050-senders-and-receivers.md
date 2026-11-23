# 50. Asynchronous work is senders and receivers whose completion rules are proved, over io_uring on Linux and a kqueue completion adapter on macOS

Date: 2026-11-23

Status: Proposed (revised 2026-11-23: files through the same senders, and `|>` pipelines with error handling proved complete)

## Context

Dean asked for `Sender` and `Receiver` abstractions in the style of Eric Niebler's work on C++ `std::execution` ([P2300](https://wg21.link/p2300), with Lewis Baker, Kirk Shoop, Michał Dominiak, Lucian Radu Teodorescu and others, in C++26). They should hide the operating system's I/O interface, and Pia should make them stronger. The proof point is io_uring on Linux and its nearest equivalent on macOS, behind one interface.

The design so far ([ADR 0027](0027-coroutines-and-race-freedom.md), [docs/concurrency.md](../concurrency.md#the-scheduler-is-pia), issue #79) has `Pia.Io` wrap kqueue as a readiness loop that parks tasks. It mentions "epoll or io_uring on a later Linux port". Nothing in it is built yet. That leaves room to choose the abstraction before the first line of I/O code.

### What P2300 is

- A **sender** describes work and does nothing until it is started. A **receiver** is where the result goes. It has three completion channels: `set_value`, `set_error` and `set_stopped`.
- `connect(sender, receiver)` gives an **operation state**, and `start(op)` runs it. The operation must then call exactly one of the receiver's channels, exactly once.
- A sender advertises its **completion signatures**: the value types, error types and whether it can stop. Generic algorithms (`then`, `let_value`, `when_all`, `upon_error`, `continues_on`, `sync_wait`) compute their own signatures from their inputs.
- A **scheduler** is a factory of senders (`schedule`) that complete on its execution context. Cancellation goes through a **stop token** that the receiver's **environment** supplies.

The model fits completion-based I/O directly: an io_uring submission is an operation state, and its completion queue entry is the receiver call.

### Where P2300 relies on the programmer

The C++ design states several rules that the compiler cannot check:

1. **Exactly once.** A receiver must get exactly one completion. Calling two, calling one twice or calling none is undefined behaviour or a hang. Only the documentation states this rule.
2. **Operation states never move.** After `start`, the operation state must stay where it is until it completes, because the kernel or another thread holds its address. Moving or destroying it early is undefined behaviour.
3. **Buffers outlive the operation, including through cancellation.** When a stop is requested, io_uring still writes into the buffer until the cancelled operation's own completion arrives. Releasing the buffer when the stop is requested, rather than when that completion arrives, is a use-after-free in the kernel's hands. Rust's async runtimes face the same problem: a future that owns an in-flight io_uring buffer can be dropped mid-flight.
4. **Stop races.** A stop request can race the completion it is cancelling. Stop callbacks must be deregistered without racing a callback that is still running. Getting this right is notoriously subtle in stdexec and libunifex.
5. **Detached work.** `ensure_started` and `start_detached` let work outlive its caller. Both were removed before C++26 ([P3187](https://wg21.link/p3187)) in favour of async scopes ([P3149](https://wg21.link/p3149)).
6. **Error types are open.** `set_error` can carry any type, so a caller cannot know it has handled every error.

Pia already has the tools to turn each of these rules into a type rule or a proof goal. `@linear` types must be consumed exactly once on every path ([stdlib.md](../stdlib.md#7-linear-resources-and-memory)). `moved` parameters transfer ownership. Closed error sets come with exhaustive handlers ([ADR 0028](0028-error-propagation-and-cleanup.md)). Structured scopes allow no detached tasks (ADR 0027). Lifetimes and regions are checked by liveness ([ADR 0042](0042-lifetimes-liveness-and-escape-analysis.md)). Generics are proved once against their concepts ([ADR 0043](0043-generic-definitions-proved-once.md)). Contracts carry through function arguments ([ADR 0044](0044-function-values-and-lambdas.md)). The model checker handles what types cannot express (ADR 0027, section 4).

### What the operating systems offer

| | Linux | macOS |
| --- | --- | --- |
| Completion-based | **io_uring**: shared submission and completion rings, one completion queue entry per submission (except multishot), a 64-bit `user_data` token, sockets and regular files, `IORING_OP_ASYNC_CANCEL`, `IORING_OP_TIMEOUT` | **Dispatch I/O** (`dispatch_io_*`): callbacks as Objective-C blocks on libdispatch's own thread pool, with `dispatch_data_t` buffers. **POSIX AIO** with `SIGEV_KEVENT`: files only, with small default limits set by `sysctl` |
| Readiness-based | **epoll**: registers the open file description, not the descriptor | **kqueue**: `EVFILT_READ`, `EVFILT_WRITE`, `EVFILT_TIMER`, `EVFILT_USER`; it removes a registration when the descriptor is closed |
| Availability | io_uring can be missing or refused: `ENOSYS` on old kernels, `EPERM` when `kernel.io_uring_disabled` is set (Linux 6.6 and later), or a container's seccomp profile | always |

macOS has no equivalent of io_uring. The candidates are kqueue with a completion adapter written in Pia, or Dispatch I/O.

## Decision

### 1. Four concepts in `Pia.Exec`

`Pia.Exec` is Pia's `<execution>` ([ADR 0040](0040-cpp23-standard-library-in-pia.md)). It defines `Receiver`, `Sender`, `Operation` and `Scheduler` as concepts ([ADR 0034](0034-concepts-and-overload-resolution.md)). Each P2300 rule that C++ only documents becomes a type rule or a law:

```ocaml
(* Designed syntax. `v` is what the work produces, `e` its closed error set. *)
let meta Receiver (r : type) (v : type) (e : type) : concept = sig
  @linear r                                       (* consumed exactly once *)
  let value   : (self : moved r) -> (x : moved v) -> unit
  let error   : (self : moved r) -> (x : moved e) -> unit
  let stopped : (self : moved r) -> unit
  let env     : (self : borrowed r) -> env        (* stop token, scheduler, allocator *)
end

let meta Operation (o : type) : concept = sig
  @linear o
  let start : (self : moved o) -> unit
end

let meta Sender (s : type) : concept = sig
  let connect : (r : type where Receiver r (value_of s) (error_of s))
             -> (self : moved s) -> (rcv : moved r) -> op_of s r
  law Operation (op_of s r)
end
```

- **Exactly once is a type rule.** A receiver is `@linear`, and each of its three channels takes it `moved`. An operation that holds a receiver must consume it on every path, by calling exactly one channel. A path that calls two channels is a use-after-move, and one that calls none fails the `@linear` check. Both are compile errors in the operation's own module. The rule holds for every receiver, including the ones the algorithms build.
- **Completion signatures are type-level metaprograms.** `value_of s`, `error_of s` and `op_of s r` are type-level metaprograms over the sender's type ([ADR 0035](0035-substitution-failure-and-total-constraints.md)), which plays the role of P2300's `completion_signatures_of_t`. `error_of s` is a closed error set, so the union in `when_all a b` is `error_of a | error_of b` ([ADR 0028](0028-error-propagation-and-cleanup.md)), and a `match` on it must be exhaustive.
- **Values carry their facts.** A value type is an ordinary Pia type, so its facts live in the type ([ADR 0037](0037-idiomatic-pia-and-lints.md)). A read completes with `{ n : usize; buf : moved [u8] } where n <= len buf`, and the bytes it wrote are `written buf 0 n`. A receiver is proved under those facts. `then s f` completes with `f`'s result and `f`'s `ensures`, proved once for every `s` and `f` (ADR 0043 and ADR 0044).
- **Operation states move freely.** Pia never gives the kernel the address of a Pia value, other than buffers, whose memory does not move when their slice value moves. A backend that needs a stable token, such as io_uring's `user_data`, uses an index into its own table of in-flight slots (section 3). C++'s immovable operation states need no counterpart.
- **No detached work.** `Pia.Exec` has no `ensure_started` and no `start_detached`. Work that must run alongside other work is spawned into a `scope` (ADR 0027), which also serves as P3149's `async_scope`: `spawn s sender`. A scope cannot end until each operation it holds has completed, because each one is `@linear`.

The first algorithms are `just`, `just_error`, `then`, `upon_error`, `let_value`, `when_all`, `continues_on`, `starts_on` and `sync_wait`. `bulk` waits for the `spread` work. `split` waits until sharing an operation's result, which needs `ref` from [ADR 0047](0047-recursive-sum-types-and-shared-references.md), comes up in practice.

### 2. I/O senders own their buffers, and cancellation is proved

`Pia.Io` offers I/O as senders: `read_some`, `write_some`, `accept`, `connect`, `recv`, `send`, `after` (a timer) and `close`. A buffer is passed `moved` into the sender, and every completion gives it back: `value` returns it with the byte count, `error` returns it with the error, and `stopped` returns it unchanged.

- **Nobody touches a buffer while the kernel owns it.** Between `start` and the completion, the buffer belongs to the backend's in-flight slot. No Pia code can read or write it, so there is no race with the kernel. This is ADR 0027's race rule with the kernel treated as one more task.
- **A buffer returns only when the kernel's completion arrives.** A stop request does not complete the operation. It asks the backend to cancel (`IORING_OP_ASYNC_CANCEL`, or deregistration on a readiness backend), and the receiver is called only when the target operation's own completion arrives. The buffer lives in the slot, and only the completion handler can take it back out, so a handler that returns it early does not type-check. That closes hole 3.
- **`stopped` means nothing happened.** When an operation was cancelled after it transferred data, such as a read that completed in the same instant, its receiver gets `value`, never `stopped`, so no data is lost. This is a law of every I/O sender. A readiness backend proves it. On io_uring it is the trusted meaning of `-ECANCELED` from io_uring_enter(2).
- **At most one read and one write in flight per stream.** A connected stream splits into a `@linear` read half and a `@linear` write half. A pending read consumes the read half, and the completion gives it back. So the type system rules out two concurrent reads on one socket, and a readiness backend needs at most one registration per direction.
- **Borrowed buffers come later.** A buffer could instead be `borrowed`, with a region that encloses the operation (ADR 0042). That is sound, because a `@linear` operation cannot be dropped before it completes. It is left for later because moving the buffer and getting it back is simpler to prove and to explain.

Inside a `@suspends` function, `wait s` connects the coroutine's frame as the receiver, as `co_await` does in C++. `value` resumes the coroutine with `Ok`, `error` with `Err`, and `stopped` with `Err Stopped` (question 1). So the read loop in [docs/concurrency.md](../concurrency.md#syntax) is unchanged. `read` is now a sender, and `wait` is how a coroutine consumes one. Senders also work without coroutines, through `then` chains and `sync_wait`. That matters because the coroutines (#77) are not built yet.

### 3. Backends: io_uring on Linux, and one proved completion adapter over kqueue and epoll

```
                    Pia.Exec concepts  (Sender, Receiver, Operation, Scheduler)
                               │
                     Pia.Io senders and io_context
             ┌─────────────────┴───────────────────┐
     Pia.Io.Uring                        Pia.Io.Ready r   (completion over readiness,
     @target(x86_64_linux)               proved once for every r : Readiness)
     native completion                   ┌──────────┴──────────┐
                                  Pia.Io.Kqueue          Pia.Io.Epoll
                                  @target(arm64_macos)   @target(x86_64_linux)
```

**Linux uses io_uring.** `Pia.Io.Uring` maps a sender's `start` to one submission queue entry. Its `user_data` is a slot index and a generation, and each completion queue entry calls the receiver held in that slot. glibc has no io_uring wrappers, and most of liburing is `static inline` code that cannot be called through FFI. So the module calls `io_uring_setup`, `io_uring_enter` and `io_uring_register` through `syscall`, and it sees the mapped rings through `unsafe view` ([stdlib.md](../stdlib.md#8-posix-trusted-declarations-and-typed-wrappers)). Ring heads and tails are read with acquire loads and written with release stores. The split between trust and proof:

- **Trusted**, with each item citing io_uring(7) or io_uring_enter(2): the kernel writes only completion entries between the head and the tail it publishes, it returns each `user_data` it was given exactly once (outside multishot), and `-ECANCELED` means the operation did not run.
- **Proved**: ring indexing by mask, which is affine and suits Presburger ([ADR 0020](0020-presburger-for-affine-goals.md)). A submission happens only when the ring has room. Every slot index taken from a completion is in bounds and in flight. Each slot is delivered once. The number of operations in flight never exceeds the table's capacity, so completion-queue overflow cannot happen. `IORING_FEAT_NODROP` is required anyway, as a belt to the braces.

**macOS uses kqueue with a completion adapter written in Pia.** `Pia.Io.Ready r` turns any readiness interface into completions. On `start` it tries the system call nonblocking. If the call returns `EAGAIN`, it registers one-shot interest (`EV_ONESHOT` or `EPOLLONESHOT`) in that descriptor's direction and parks the operation in its slot. When the event fires, it retries the call, and either completes or rearms. The adapter is generic over a `Readiness` concept (`register`, `rearm`, `deregister`, `wait events timeout`, `wake`), so it is proved once (ADR 0043). `Pia.Io.Kqueue` and `Pia.Io.Epoll` are its two models, each `@target` of its own platform ([ADR 0049](0049-targets-are-theories.md)). Each model differs only in what it trusts:

- Cross-thread wakeups use `EVFILT_USER` on kqueue and an `eventfd` on epoll.
- Timers are a proved heap in Pia (`Pia.Core.Algo.Heap`) that drives the wait's timeout. That costs no system call per timer, and it is the same code on both platforms. io_uring uses `IORING_OP_TIMEOUT`.
- epoll registers the open file description, so a descriptor that is closed while registered can leave a stale registration behind if it was `dup`ed. A registration is therefore `@linear`, and `close` takes the registration first, which makes `EPOLL_CTL_DEL` before `close` a type rule. kqueue removes a registration on close, and the same rule costs it nothing.
- Regular files are always "ready" to a readiness API, yet their reads can still block on the disk. So the adapter sends file operations to the blocking pool (`offload`, [docs/concurrency.md](../concurrency.md#blocking-calls)), as libuv and Tokio do. io_uring runs them natively.

**Dispatch I/O is rejected for now.** Its callbacks are Objective-C blocks, which would need the blocks ABI in FFI. It runs on libdispatch's own thread pool, whose interleavings Pia cannot see, so race and deadlock proofs would stop at its boundary. It owns its buffers as `dispatch_data_t`, so the moved-and-returned ownership of section 2 does not apply. Its file I/O is a thread pool anyway, and that pool competes with `Pia.Task`'s workers for the same cores. It could come back later as a separate scheduler, for interoperating with Apple frameworks.

**The backend is chosen at run time on Linux.** `io_context.create` tries `io_uring_setup`. If that fails with `ENOSYS` or `EPERM`, it falls back to `Ready Epoll`. The context is a variant of the two backends, so a submission costs one `match`. Both backends satisfy the same sender laws, so a program's proofs do not depend on which one runs. On macOS there is only `Ready Kqueue`, chosen at compile time through `when Target.is arm64_macos`. Linux CI runs the I/O tests twice, once with each backend (with `PIA_IO=epoll` to force the fallback), and macOS CI runs them once.

**No allocation per operation.** The in-flight table is allocated once, when the context is created, from the allocator it is given, and that allocation can fail like any other (ADR 0026). After that, `start` never allocates. A full table is back-pressure: the `schedule` sender waits for a free slot. A context is `@linear`, and `close` requires its table to be empty, so it cannot be closed with work in flight.

### 4. The stop race goes to the model checker

Each in-flight slot is a small state machine: free, submitted, cancel requested, completed, free. A stop request from another thread races the completion handler. The goal is that every slot delivers exactly one completion, and that a stop callback is never running after its slot is freed. That is a protocol goal for the model checker (ADR 0027, section 4, issue #81), proved once for the slot table and the stop-token implementation, and not per program. Until the model checker exists, `Pia.Io` accepts stop requests only from its own run-loop thread, where the race cannot happen. A cross-thread stop is an unproved goal that `--allow-unproved=race:` must accept.

### 5. Files, pipes and sockets share one set of senders

Nothing in sections 1 to 4 is specific to sockets. `Pia.Io`'s senders cover every kind of descriptor:

- **Streams and files alike.** `read_some` and `write_some` work on any descriptor: a file, a pipe, a socket or a terminal. Files also get positional `read_at` and `write_at` (`pread` and `pwrite`), whose footprints are byte ranges, so tasks that write disjoint ranges of one file are proved race-free by FPL ([docs/concurrency.md](../concurrency.md#resources-other-than-memory)). The flagship demo's parallel tile writes need exactly that.
- **File operations are senders too.** `open` (`openat`), `close`, `fsync`, `stat`, `rename` and `unlink` are senders. `read_all` and `write_all` are senders composed from the others, proved to transfer exactly the buffer's length or to fail.
- **The backend chooses how, per descriptor kind.** `open` returns a `file`, and `accept`, `connect` and `pipe` return a `stream`, so the choice is static. io_uring runs all of them natively (`IORING_OP_READ`, `WRITE`, `OPENAT`, `STATX`, `FSYNC` and `CLOSE`). The readiness adapter runs streams through kqueue or epoll and sends file operations to the blocking pool, since readiness says nothing useful about regular files. It is the same sender with the same laws either way, so the caller cannot tell the difference.
- **Cancelling a file operation on the blocking pool** completes it as `stopped` only if it had not started. A `pread` that is already running cannot be interrupted, so it completes with its value, and the law that `stopped` means nothing happened still holds.
- **Blocking I/O is the same layer.** The `reader` and `writer` concepts of `Pia.Io` ([docs/stdlib.md](../stdlib.md), [docs/cpp-std.md](../cpp-std.md)) are implemented over these senders, and the blocking forms are `sync_wait` of them. There is one I/O layer, not a blocking one beside an asynchronous one.

### 6. Pipelines: `|>`, with every error case proved handled

A sender adapter takes the sender as its last argument, `then f s`, and the prelude operator `|>` passes its left side as the last argument of its right side: `s |> then f` is `then f s`. It is defined by a metaprogram, as every operator is ([ADR 0008](0008-operators-via-metaprograms.md)). P2300 spells this `|`, but in Pia `|` already separates match arms and variants, and `|>` is OCaml's and F#'s spelling for the same idea. A pipeline is then dataflow between senders, written in the order it runs:

```ocaml
(* Designed syntax. *)
let load_config (path : cstr) (buf : moved [u8]) =
  open path o_rdonly                                   (* errors: OpenError *)
  |> let_value (let (f) => read_all f buf)             (* ... | IoError *)
  |> then parse_config                                 (* ... | ParseError *)
  |> recover (let (e) =>
       match e with
       | ParseError _ -> just default_config
       | NoEntry -> just default_config)
(* value_of: config.  error_of: (OpenError | IoError) without NoEntry *)
```

- **Errors flow through the types.** Each stage's error set is the union of its inputs' error sets ([ADR 0028](0028-error-propagation-and-cleanup.md)). `recover` and `upon_error` take a handler whose `match` is checked against that set, and the cases it handles are removed from the set: the stage's `error_of` is the remainder, computed by a type-level `without` on closed error sets. An arm for an error that cannot reach it is an error, as an unreachable arm always is.
- **A pipeline must end with nothing left unhandled.** A pipeline ends in `sync_wait`, which returns a `result` that the caller must `match`; in `wait`, whose `Err` arms or `handle` block must cover the set; or in `spawn` into a scope, whose handler must cover it. There is no way to start a sender and drop its errors, so an unhandled error is a compile error, never a run-time unwind.
- **Values carry their facts forward.** `then f` is proved under the facts of the previous stage's value type (section 1), so `parse_config` may assume that `read_all` filled its buffer, and the pipeline's own value has `parse_config`'s `ensures`.
- **Resources come back on every path.** A buffer moved into a stage comes back in that stage's value or in its error, so a handler that recovers from `IoError` gets the buffer back to reuse or free, and the `@linear` rules check that it does.
- **Fan-out and fan-in** are `when_all a b c` (variadic, [ADR 0051](0051-variadic-generics-and-foreign-varargs.md)), with `split` later. A channel from ADR 0027 bridges in both directions: `recv ch` and `send ch x` are senders. A pipeline of senders is acyclic by construction, because values only flow forward, so only channels can close a cycle, and ADR 0027's channel topology check covers those.

**Why this is stronger than exceptions.** An exception can be of any type, thrown from any call, and it is invisible in signatures: C++ has only `noexcept` or nothing. Through asynchronous boundaries it travels as a type-erased `exception_ptr`, and no compiler checks that a handler exists for what can reach it. Here, every pipeline's error set is in its type and is closed, every handler is checked exhaustive against it, what a handler removes is gone from the type, the end of every pipeline must have handled the rest, and cleanup is by linearity, with resources returned along the error path too.

### 7. What this changes

- **ADR 0027 and issue #79.** `Pia.Io` offers senders instead of a parking API, and the kqueue loop becomes one backend of several. `Pia.Task`'s scheduler is a `Scheduler`, and `spawn s x` accepts a sender as well as a closure. The `@blocking` and `offload` rules are unchanged.
- **The earlier poller plan** (a readiness poller as the public I/O interface) becomes `Pia.Io.Ready`'s internal `Readiness` concept.
- **C++ mapping.** [docs/cpp-std.md](../cpp-std.md) gains `<execution>` mapped to `Pia.Exec`.
- **Blocking `Pia.Io`** (stdlib.md, section 8) becomes `sync_wait` over the same senders (section 5).

## Prerequisites, in order

1. **FFI** (#55): variadic foreign calls, as [ADR 0051](0051-variadic-generics-and-foreign-varargs.md) section 6 designs them (`syscall`, `open` and `fcntl` are variadic, and Apple arm64 passes variadic arguments on the stack), C structs passed as byte buffers (`sockaddr`, `kevent`, `epoll_event`, `io_uring_sqe`), and `errno` (`__error` on macOS, `__errno_location` on glibc).
2. **`@target` items and `when Target.is`** (ADR 0049, step 3c, PR #292).
3. **`Pia.Sys.Posix`, `Pia.Sys.Fs` and `Pia.Sys.Net`** (#57), blocking and per target: constants, `sockaddr` (macOS has a `sin_len` byte, Linux does not), the packed `epoll_event` on x86_64, and `SO_NOSIGPIPE` versus `MSG_NOSIGNAL`.
4. **`Pia.Mem` as a module** (#59), for buffers and the in-flight table.
5. **Tuples and variadic generics** (ADR 0051), for `when_all` over any number of senders. **Function values stored in data** (ADR 0044, a later step), because an operation state holds its receiver and `then`'s function, and **acquire and release atomics on foreign memory**, for the io_uring rings.
6. **`Pia.Exec`**: the concepts and algorithms, with an inline scheduler and `sync_wait`, the `|>` operator, and `recover` with the type-level `without` on error sets. It is pure Pia with no system calls, so it can be proved and tested first.
7. **`Pia.Io.Ready`, `Pia.Io.Kqueue` and `Pia.Io.Epoll`**, the run loop and the timer heap, with a proved echo server as the demo, tested on both CI jobs.
8. **`Pia.Io.Uring`**, and the Linux run-time choice between the two backends.
9. **Cross-thread stop**, when the model checker lands (#81). **`wait` on senders**, when coroutines land (#77).

## Consequences

- Every P2300 rule listed under "Where P2300 relies on the programmer" is checked. Exactly-once completion and the absence of detached work are type rules. Buffer ownership during I/O and through cancellation are type rules too. Closed error sets come with exhaustive handlers. The stop race is a model-checker goal.
- Files, pipes and sockets go through one set of senders, and blocking I/O is `sync_wait` of them.
- Pipelines written with `|>` are checked to handle every error that can reach their end, which exceptions cannot offer.
- One interface hides three backends. Only the system-call contracts differ between them, and they are listed per target in the trust report.
- On macOS, completion is emulated, so an operation can cost one extra system call compared with io_uring, and file I/O runs on the blocking pool. Pia does not claim equal performance across the two platforms, only the same semantics.
- The I/O stack is larger than a bare poller. Its lower layers are still needed (`Pia.Sys`), and the poller survives as `Readiness` inside the adapter.
- `wait` gets a precise meaning: it connects a coroutine frame to a sender.

## Questions for Dean

1. **Is `stopped` its own channel, or a member of the error set?** The recommendation is to keep it separate in `Receiver`, as P2300 does, because a stop is not a failure and generic algorithms treat it differently. `wait` and `?` map it to `Err Stopped`, so handlers must cover it explicitly.
2. **Should Linux fall back to epoll at run time?** The recommendation is yes. io_uring is disabled on some kernels and in some containers, and the fallback costs one `match` per submission. The alternative is io_uring only, with a clear error when it is missing.
3. **On macOS, do regular files go to the blocking pool, or through POSIX AIO with `SIGEV_KEVENT`?** The recommendation is the blocking pool first. AIO is a true completion API for files, but its default limits are small and it does not cover sockets.
4. **When do streams of completions arrive?** io_uring's multishot `accept` and `recv`, and repeating timers, complete many times, which is not a sender. The recommendation is to loop over single-shot senders in v1, and to add sequence senders, in the style of [P2849](https://wg21.link/p2849), in their own ADR.
5. **Module name.** `Pia.Exec` follows `std::execution`. `Pia.Async` would be the alternative.

## Prior art

| Source | What Pia takes |
| --- | --- |
| P2300 `std::execution`, stdexec, libunifex | senders, receivers, operation states, three completion channels, schedulers, environments, stop tokens |
| P3149 `async_scope`, P3187 | scoped spawning instead of detached work |
| tokio-uring, glommio, monoio | buffers moved into the operation and returned with the completion |
| libuv, Tokio | completion over readiness, and file I/O on a blocking pool |
| Austral, ATS linear types | consuming a resource exactly once, as a type rule |
