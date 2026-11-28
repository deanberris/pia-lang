# 82. Release 0.3.0: a SQL DSL and a proved embedded database, and its gates

Date: 2026-11-28

Status: Proposed

## Context

The [roadmap](../roadmap.md) (Dean, 2026-11-27, agreed 2026-11-28) makes 0.3.0 the release for data processing at the scale of a whole machine. Its demo is a small SQL server written in Pia: the 0.2.0 embedded REPL takes SQL (or the Pia DSL) from clients, compiles and runs it on the CPU's cores and SIMD units and on the GPU, over a proved embedded database.

Dean's decisions that shape it (2026-11-27):

- **Each query is compiled in its own embedded REPL session**, isolated from the server's and from other queries' sessions. The session proves the query and exports a function reference that fits a fixed query interface; the execution engine calls it, so the compiled query drives the engine rather than an engine interpreting a plan. Sessions run on a fixed pool of tasks, each with its own arena, and share as little as possible.
- **Scope is SQL:2023** (ISO/IEC 9075:2023) without SQL/PGQ property-graph queries, which wait for a graph theory after 1.0. The demo builds up through selects, filtering, joins and grouping to analytical queries: window functions, common table expressions including recursive ones, and `GROUPING SETS`, `ROLLUP` and `CUBE`.
- **A second demo, an OS in Pia** that only hosts a web server giving access to a Pia REPL, lands in 0.3.x or 0.4.x, because any OS that touches storage needs the raw block devices this release builds.

## Decision

The release policy of [ADR 0080](0080-release-0-1-0-gates.md) applies.

### Libraries, which gate the 0.3.0 tag

1. **The SQL DSL.** Queries as metaprograms that expand at compile time into typed, proved Pia: a schema is a record type and a query is checked against it. SQL text parses to the same tree. The plan lowers through `@lower` and `spread` the way 0.1.0's kernels do.
2. **A theory of relational algebra**: select, project, join, group and aggregate, with bag semantics and SQL's three-valued `NULL` logic, so each plan rewrite (predicate pushdown, join reordering, aggregate splitting) is proved to keep the query's meaning.
3. **Query sessions**: a query compiled in its own 0.2.0 REPL session, exporting a function reference of the query interface, with its memory in its task's arena and freed with it.
4. **Block I/O.** A `Pia.Sys` layer for block devices, with a theory of what a device promises after `fsync` and on a torn write; first over memory-mapped files that simulate raw disk, then over raw devices on Linux.
5. **A proved embedded database library**: pages, an index, a write-ahead log and crash recovery, each proved against a model. A committed transaction survives a crash, an uncommitted one leaves no trace, and an index agrees with its table. The first index is a B-tree, unless the design ADR finds an LSM tree better for the demo.
6. **Parallel and GPU operators**: scans, hash joins, sorts and aggregates over columnar buffers, using 0.1.0's vectorisation and GPU paths.

### The demo, which closes the 0.3.x series

- The server answers clients over the network (the wire protocol is chosen in its ADR), with each query proved and compiled in its own session.
- It runs a published query set in order of difficulty: selects and projections, filters, inner, outer, semi and anti joins, grouping with aggregates, then window functions, CTEs (recursive too), `GROUPING SETS`, `ROLLUP` and `CUBE`. Results match a reference database on the same data.
- A crash test kills the server at random points under load and checks, on restart, that every committed transaction is there and no uncommitted one is.
- It reports throughput on every core, the SIMD units and the GPU, against a single-threaded run.

### The second demo, in 0.3.x or 0.4.x

An OS in Pia that boots, sets up memory and page tables, drives a network device and a block device, and serves a Pia REPL over the 0.2.0 HTTP/2 stack, proved with nothing else underneath. It needs the bare-metal side of `Pia.Target` ([ADR 0049](0049-targets-are-theories.md)) and a trusted-item story for hardware, each its own ADR. It does not hold up the close of 0.3.x; it lands in the first release where it is complete.

## Consequences

- The relational algebra theory and the crash model are large proofs; their cost is tracked on the proof benchmark like any library.
- Per-query sessions make session start-up cost part of query latency, so 0.2.0's measurements of it matter here.
- Graph queries are left out on purpose, and the docs say so.

## Open questions

Answered when the work starts: whether the crash model is per page or per sector; B-tree or LSM tree first; and the wire protocol.
