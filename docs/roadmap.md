# Roadmap to 1.0

Pia reaches 1.0 in five releases. Each one is defined by a demo: a working program, proved before it compiles, that shows something other languages cannot show at that cost. Each release also builds what the next one needs.

| Release | The demo that completes it | What it brings you |
| --- | --- | --- |
| [0.1.0](#010-proved-numerics-on-apple-silicon) | Stream delineation, sediment transport and a small LLM, on an Apple Silicon Mac's CPU and GPU | Floats with proved error bounds, linear algebra, `spread`, GPU kernels written in Pia |
| [0.2.0](#020-an-embeddable-repl-and-proved-networking) | A service hosting a Pia REPL, reprogrammed from a control plane while it serves gRPC | Pia as a library inside other programs; proved HTTP/2; gRPC and Protocol Buffers from `.proto` files |
| [0.3.0](#030-a-sql-dsl-and-a-proved-embedded-database) | A small SQL server written in Pia, using every core, the SIMD units and the GPU | Queries checked against their schema at compile time; a crash-safe embedded database; block I/O |
| [0.4.0](#040-calling-c) | Pia driving MLIR and LLVM through their C++ APIs | Bindings to C++ libraries, with templates, exceptions and ownership carried across |
| [0.5.0](#050-a-sat-and-smt-solver-written-in-pia) | A SAT, then SMT, solver written in Pia, running beside Z3 | A proved solver, parallel and vectorised, that certificates can name |
| [1.0](#10-pia-written-in-pia) | Pia's front end, written in Pia, compiling the standard library and every earlier demo | A self-hosted compiler over Pia IR, still lowering through MLIR and LLVM |

## How releases ship

A release's libraries ship in its `.0` (0.2.0, 0.3.0, and so on), as soon as they are built, proved and documented. Patch releases (0.2.1, 0.2.2, ...) keep coming until its demo is complete, and the release with the finished demo closes the series. So you can use a release's libraries before its demo is done.

Every release, `.0` and patch alike, is built by CI from a proved tree: the build, the tests and the proof benchmark pass on Linux and macOS, and every goal in the standard library is proved with nothing accepted outside named trusted items (`piac --trust-report` lists them). The [ADRs](adr/README.md) for each release (0080 to 0085) give the exact gates.

## 0.1.0: proved numerics on Apple Silicon

Programs that use the whole of an M-series Mac, the GPU and the CPU's SIMD units, and are still proved.

- **Stream delineation** over a terrain heightmap ([done](streams.pia.md)) and **sediment transport** as a fixed-point model ([done](sediment.pia.md)), first on one core, then on every core with `spread`, then on the GPU.
- **A small LLM**: llama2.c's TinyStories model, ported from PyTorch, with shapes, bounds, finiteness and each kernel's float error proved, running on the CPU's SIMD units and with its matrix products on the GPU ([ADR 0067](adr/0067-release-0-1-0-a-proved-small-llm.md)).

It brings `f32` and `f64` with real-valued specifications and rounding error, `Pia.Math` without libm, linear algebra kernels, `@lower` and `@schedule` for writing compiler lowerings in Pia, and GPU code generation through SPIR-V and Metal. [ADR 0080](adr/0080-release-0-1-0-gates.md) gives the gates.

## 0.2.0: an embeddable REPL and proved networking

Pia runs inside other systems, and talks to the network through libraries proved against models of the protocols.

The demo is a service that hosts a Pia REPL. A control plane sends it new definitions, which it proves and installs while it runs, and a data plane serves gRPC requests through whatever was installed last. A definition that fails to prove is refused, and the service keeps serving the old one.

It brings the REPL as a library with a C ABI and a Pia interface, with many isolated sessions in one program; theories of TCP streams and HTTP/2; a fast HTTP/2 server and client proved against them; TLS through BoringSSL, with contracts checked where Pia calls it; and a gRPC plugin that turns `.proto` files into Pia types, proved encoders and decoders, and service interfaces. QUIC and HTTP/3 follow if the same TLS binding covers them. [ADR 0081](adr/0081-release-0-2-0-gates.md) gives the gates.

## 0.3.0: a SQL DSL and a proved embedded database

Data processing at the scale of a whole machine, with the storage engine proved.

The demo is a small SQL server written in Pia. It takes SQL (or the same queries written in Pia), compiles each query in its own embedded REPL session, and runs it on every core, the SIMD units and the GPU, over a database whose crash safety is proved. It covers SQL:2023 without property-graph queries: selects, filters, joins and grouping, then window functions, common table expressions and `ROLLUP` and `CUBE`.

A second demo follows in a 0.3.x or 0.4.x release: a small operating system written in Pia whose only job is to serve a Pia REPL over HTTP/2, which needs the raw block devices 0.3.0 builds. [ADR 0082](adr/0082-release-0-3-0-gates.md) gives the gates.

## 0.4.0: calling C++

Pia binds to C++ interfaces, and the release shows that Pia can express everything a C++ interface can.

The demo is Pia code that builds an MLIR module, runs a pass pipeline and emits an object through MLIR's and LLVM's C++ APIs, with contracts on the calls it makes. Bindings are generated from headers; templates become Pia metaprograms checked against Clang's instantiations; C++ exceptions arrive as boxed error values; RAII objects become Pia values with `drop`. [ADR 0083](adr/0083-release-0-4-0-gates.md) gives the gates.

## 0.5.0: a SAT and SMT solver written in Pia

The prover Pia trusts can itself be written in Pia, proved, and fast enough to run beside Z3 on the goals `piac` emits.

The demo is a CDCL SAT solver whose `unsat` answers carry checkable proofs, using threads, SIMD and the GPU, then an SMT layer for the theories Pia's own code uses most. Certificates name the engines that proved them, and Z3 stays alongside until after 1.0. [ADR 0084](adr/0084-release-0-5-0-gates.md) gives the gates.

## 1.0: Pia written in Pia

Pia's front end is written in Pia, works over [Pia IR](adr/0079-pia-module-format.md), and lowers to MLIR and LLVM, so Pia keeps up with the open-source compiler state of the art.

The demo is the Pia front end compiling the standard library and every earlier demo, with output that matches the C++ compiler's. 1.0 also brings Pia bindings for MLIR and LLVM. The C++ compiler stays as the bootstrap until Pia 3.0. [ADR 0085](adr/0085-release-1-0-gates.md) gives the gates.

## After 1.0

A growing catalogue of theories (numerics, geometry, network protocols, storage, concurrency, graphs and more), each domain starting as trusted items and proved step by step; domain languages built as separate projects on metaprograms and `@lower`; Windows, Linux on arm64 and WebAssembly as targets; and a solver path that no longer needs Z3.

## How the work is tracked

Each release has a GitHub project, and every issue carries labels:

- **Release**: `release: 0.1.0` to `release: 1.0`, or `release: post-1.0`.
- **Priority**: `P0` blocks the release's `.0` tag, `P1` blocks its demo, `P2` should land in it, `P3` could slip to the next release, and `P4` is nice to have.
- **Area**: `infra`, `performance`, `code health`, `documentation` or `demos`, where one fits.

See [Status](status.md) for what works today.
