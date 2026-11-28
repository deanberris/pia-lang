# 81. Release 0.2.0: an embeddable REPL and proved networking, and its gates

Date: 2026-11-28

Status: Proposed

## Context

The [roadmap](../roadmap.md) (Dean, 2026-11-27, agreed 2026-11-28) makes 0.2.0 the release where Pia runs inside other systems and talks to the network through proved libraries. Its demo is a service that hosts a Pia REPL: a control plane sends it definitions, which it proves and installs while running, and a data plane serves gRPC through whatever was installed last. A definition that fails to prove is refused, and the old one keeps serving.

Where things stand: the REPL ([ADR 0031](0031-verified-repl-and-live-environment.md)) is a process with JSON and MCP front ends, with live redefinition and `old` state migration. Sockets and files as senders and receivers ([ADR 0050](0050-senders-and-receivers.md)) are designed, and protocol checking with Spacer ([ADR 0053](0053-protocols-checked-by-z3.md)) is accepted. Nothing of HTTP/2, TLS or Protocol Buffers exists.

Dean's decisions that shape it (2026-11-27 and 2026-11-28):

- No cryptography in Pia for now ("a full-on rabbit hole that is best reserved to the experts"). TLS binds BoringSSL, which is Apache 2.0 with no GPL code: its C calls are trusted items first, then wrapped in a Pia module whose contracts are checked at the boundary, the way `Pia.Sys.Posix` overlays contracts on generated bindings ([ADR 0057](0057-posix-module-per-target-behind-one-interface.md)).
- The wrapper starts with what HTTP/2 needs, and covers QUIC and HTTP/3 if it can (Dean, 2026-11-28).
- 0.3.0 compiles each SQL query in its own REPL session, so the embedding API must support many isolated sessions in one program from the start, run on a fixed pool of tasks, each with its own arena.

## Decision

The release policy of [ADR 0080](0080-release-0-1-0-gates.md) applies: 0.2.0 is tagged when the libraries below are done, and the 0.2.x series closes when the demo is complete.

### Libraries, which gate the 0.2.0 tag

1. **The embeddable REPL core.** A library with a C ABI and a Pia interface: create and drop any number of isolated sessions (own definitions, proof state and allocator), submit cells, read proof results and costs, and take exported function references that stay valid while the session lives. Sessions run on a fixed task pool, each task with its own arena ([ADR 0041](0041-allocator-semantics-as-a-theory.md), [ADR 0042](0042-lifetimes-liveness-and-escape-analysis.md)). Each cell runs under a per-cell bound on proof time and memory, and exceeding it refuses the cell rather than stalling the host. Redefinition defines what in-flight calls see: a call that started keeps the definition it started with.
2. **Networking theories and models.** A theory of TCP byte streams over ADR 0050's senders and receivers; theories of HTTP/2 framing, streams, flow-control windows, HPACK and the connection state machine (RFC 9113, RFC 7541), each a theory plus a model the implementation is proved against.
3. **TLS through BoringSSL.** `Pia.Tls`: generated bindings to the calls a TLS 1.3 client and server need (context and session set-up, ALPN for `h2`, handshake, read, write, shutdown, errors), trusted at first, then wrapped with contracts on buffer lengths, handshake and session states, and error codes, checked at the boundary. Each trusted call appears in `--trust-report`. BoringSSL builds from source under Bazel and is pinned, and its licence is audited (no GPL, and its Go-licensed test code is not linked).
4. **A proved, fast HTTP/2 server and client,** `Pia.Http2`: no frame is read past its length, windows never go negative, every stream reaches a final state, and HPACK's dynamic table stays within its bound. Benchmarked against nghttp2 and the Rust `h2` crate for requests per second and latency, reported, not gating.
5. **The gRPC plugin.** A metaprogram that reads `.proto` files (proto3) and generates Pia: message types, a Protocol Buffers theory (wire types, varints, field presence, unknown fields), a model per message, and encoders and decoders proved against it; services become interfaces, and gRPC framing runs over `Pia.Http2`. Its output for a fixed set of `.proto` files is checked against `protoc`'s encodings byte for byte.
6. **Protocol checking** of the session types between control plane, REPL and data plane (ADR 0053).

### The demo, which closes the 0.2.x series

- The service runs on macOS arm64 and Linux x86_64. A scripted control plane installs, replaces and rolls back definitions while a load generator keeps calling the data plane; no request fails across a replacement, and a definition that fails to prove is refused with its failed goal reported to the control plane.
- The trust report lists exactly BoringSSL's calls and the OS's socket calls, each with its contract.
- The demo is written up on pia-lang.dev, with its proof report and benchmark.

### Stretch, which does not gate

QUIC (RFC 9000) and HTTP/3 (RFC 9114), using BoringSSL's QUIC interface, with theories for QUIC's streams, flow control and loss recovery. They land in a 0.2.x patch only if they are library additions on the same binding; otherwise they move to a later release.

## Consequences

- From 0.2.0, people embed Pia, so the REPL's C ABI and the session interface fall under ADR 0073's migration rules, and breaking changes need migrations.
- The trusted base grows by BoringSSL, named call by call in the trust report. Replacing it is not planned.
- The embedding API is designed for 0.3.0's per-query sessions, so its cost per session (memory and start-up) is measured and published.

## Open questions

Answered when the work starts, each as its own ADR: the C ABI of an embedded session; the per-cell proof budget and how a host sets it; and the exact BoringSSL call list and its contracts.
