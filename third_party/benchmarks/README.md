# Benchmark reference programs

The C, C++, Rust and Zig programs that `bench/codegen` runs against Pia (ADR 0075), one directory per suite, each with that suite's licence. Nothing here is linked into Pia or its release.

| Directory | Suite | Licence | Commit |
| --- | --- | --- | --- |
| [plb2](plb2) | [plb2](https://github.com/attractivechaos/plb2) | CC0 1.0 | `1181b3b83fea52ee85a66548845f8bf92e33fb67` |

Sources are upstream's, unmodified. A program that must change (a newer compiler's syntax, an input read from the command line rather than fixed, so that the compiler cannot specialise on it) gets a `.patch` beside it, applied by a genrule. Never vendor a GPL program.
