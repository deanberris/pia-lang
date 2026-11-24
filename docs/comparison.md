# Pia and other verified languages

Pia is not the first language to prove programs correct, and it borrows from most of the ones on this page. This page says, for each of the closest languages and tools, what they share with Pia, where Pia differs, and where they are ahead. It tries to be specific and fair: every one of them is more mature than Pia, which has not reached a 0.1 release ([status](status.md)).

## In one table

| | How goals are proved | Default integers | Compiles to | Memory | Metaprogramming | Interactive loop |
| --- | --- | --- | --- | --- | --- | --- |
| **Pia** | Interval analysis, then Z3, automatically; lemmas and `@by` tactics when that is not enough | Machine integers, overflow is a goal | Native code through MLIR and LLVM | No GC; explicit, fallible allocators | `let meta` from day one; generated code is proved like hand-written code | `pia repl` proves every cell; `pia mcp` serves it to agents |
| **Dafny** | Boogie, then Z3, automatically, with hints and lemmas | Unbounded `int`; machine types by `newtype` | C#, Java, JavaScript, Go, Python | Garbage-collected targets | None | IDE that verifies as you type |
| **F\*** | Z3 plus tactics (Meta-F\*), over dependent types and effects | Unbounded `int`; machine integer libraries | OCaml, F#; C through Low\* and KaRaMeL | GC, or manual in Low\* | Meta-F\* | Incremental checking in the editor |
| **Lean 4** | Tactics and automation (`simp`, `omega`, `grind`), checked by a small kernel | Unbounded `Nat`/`Int`; `UInt8` and friends wrap | C, with reference counting | Reference counting | Hygienic macros and elaborators, very strong | Infoview and `#eval` |
| **Idris 2** | Proofs as programs, written by hand; totality checking | Unbounded `Nat`/`Integer` | Chez Scheme and others | GC | Elaborator reflection | REPL and interactive editing with holes |
| **ATS** | Proofs as terms, plus a constraint solver for static indices | Indexed integers | C | No GC needed: linear types | Templates | None to speak of |
| **SPARK** (Ada) | GNATprove, through Why3, to Alt-Ergo, CVC5 and Z3 | Machine integers, overflow is a check to prove | Native code through GNAT | No GC; ownership for pointers | Ada generics | IDE; no REPL |
| **Liquid Haskell** | Refinement types checked by Z3, with refinements inferred | Haskell's `Int` and `Integer` | Native code through GHC | GC | Template Haskell | GHCi, but proofs run in the plugin |
| **Rust verifiers** (Kani, Prusti, Verus, Creusot) | Bounded model checking (Kani, through CBMC) or deductive proof (Prusti through Viper, Verus through Z3, Creusot through Why3) | Machine integers; overflow panics in debug builds, wraps in release | Native code through rustc and LLVM | No GC; the borrow checker | Rust macros, which the verifiers see expanded | None; a separate tool run |
| **Why3** | Many provers (Alt-Ergo, CVC5, Z3, Coq, Isabelle) over WhyML | Unbounded, with machine-integer libraries | Extraction to OCaml and C | Depends on the extraction | None | Proof sessions in its IDE |

The table is a summary. Each tool has more options than one cell can hold, and the sections below say what matters.

## What sets Pia apart

These are the choices that, taken together, no other language on this page makes.

- **Proving is compiling.** There is no separate verifier to run, and no mode where contracts are comments. `piac` proves every goal and refuses to compile while one fails or is unproved, unless `--allow-unproved` accepts it ([ADR 0004](adr/0004-strongest-guarantee-by-default.md)). Dafny comes closest: it verifies before it compiles by default, and it can be told not to.
- **The strongest guarantee is the default, on machine integers.** A `u8` is a byte, and `a + b` on two of them raises a goal that it does not overflow. Wrapping, saturating and trapping arithmetic exist, and each is something you ask for ([the tour](tour.md)). SPARK shares this; Dafny, Lean, Idris and F\* default to unbounded mathematical integers, which is easier to prove and further from the machine.
- **Cheap reasoning first.** Interval analysis settles the easy goals before Z3 sees them, and a goal Z3 refutes comes back as a counterexample: concrete inputs that break the code ([how verification works](verification.md)).
- **Built on MLIR.** Goals live in Pia's own MLIR dialects, next to the code they are about, and the code goes through LLVM to native instructions with every proved check erased. A proved index has no bounds check, and the facts the proofs establish are planned to drive vectorisation ([ADR 0011](adr/0011-mlir-and-z3-implementation.md), [ADR 0013](adr/0013-auto-vectorisation.md)).
- **Metaprogramming is part of the language, and its output is proved.** Operators are metaprograms in the prelude, `@derive` writes functions, and tactics are metaprograms that write proof steps. Whatever a metaprogram generates is verified like code you wrote ([metaprograms](meta.md)). Lean's macros and elaborators are at least as strong; Dafny, SPARK and Why3 have none.
- **Proofs travel with the binary.** Each object carries a certificate of the interfaces it provides and requires, and a library whose interface changed cannot bind to a program that was proved against the old one, because the witness symbols the loader must bind are missing ([shared libraries and certificates](abi.md)). Most verifiers stop at the source: once compiled, nothing records what was proved.
- **A verified REPL, and an MCP server for agents.** `pia repl` proves every cell before it runs, refuses a redefinition that would break a caller, and swaps proved code into running tasks ([the REPL](repl.md)). `pia mcp` serves that session to an agent, and teaches it the language: a primer when it connects, `:help` topics, hints on failed cells and what each proof cost. Lean and Idris have excellent interactive loops, but they check code and run it as separate steps; Pia's REPL never runs a cell it has not proved.
- **No garbage collector, ever.** Allocators are explicit and every allocation can fail ([ADR 0026](adr/0026-memory-manager.md)), as in SPARK, ATS and Rust.

## Where the others are ahead

Pia's choices have costs, and the other languages have years of work Pia does not.

- **Maturity.** Dafny, SPARK, F\*, Lean and Liquid Haskell have been used for real systems for a decade or more. SPARK is used in avionics and security work, F\* produced the HACL\* cryptography in Firefox and the Linux kernel, and Lean has Mathlib. Pia compiles a subset today, for one target (arm64 macOS); floats, recursive types and much of the concurrency design are not built yet ([status](status.md#known-limitations)).
- **Expressiveness.** Lean, F\* and Idris have dependent types, so a type can say almost anything, and a proof can be as long as it needs to be. Pia's goals are first-order formulas that Z3 decides or gives up on. A property that needs induction needs a lemma, and some nonlinear or deeply quantified goals will not prove automatically at all.
- **The trusted base.** Lean checks every proof with a small kernel, so a bug in a tactic cannot prove something false. Pia trusts Z3, the way the verifier encodes goals for it, and the compiler. Its certificates record which interfaces were proved, not proofs that someone else can check, and the planned `pia-cert audit` re-checks obligations with your own Z3, not the machine code ([trust model](abi.md#trust-model)).
- **Prover choice.** Why3 and SPARK send a goal to several provers and keep the one that succeeds. Pia uses Z3 alone, with solver strategies (`@solver`) as the escape hatch.
- **Bounded model checking.** Kani checks Rust code bit-precisely, unsafe code included, up to a bound, with no invariants to write. Pia needs a loop invariant for each loop, and has nothing like Kani for code that is not Pia.
- **Ecosystems.** Rust, Haskell and Ada have libraries for everything. Pia's standard library is being written in Pia, over a small POSIX core ([standard library](stdlib.md), [the C++ standard library in Pia](cpp-std.md)).

## Language by language

### Dafny

The closest in how it feels: an imperative and functional language with `requires`, `ensures`, loop invariants and `decreases`, proved automatically by Z3, with lemmas for the hard parts. Dafny's `int` is unbounded and it compiles to languages with garbage collectors, so it is often used to write and prove an algorithm that is then shipped in C#, Java or Go. Pia proves the machine-level program itself: fixed-width integers, slices with lengths, no GC, and native code with the checks erased.

### F\*

F\* combines dependent types, an effect system, Z3 and tactics, and its Low\* subset compiles to C that ships in Firefox and the Linux kernel. It can state far more than Pia can, and its proofs can be as manual as needed. Pia gives up dependent types for a smaller, automatic logic and an ML syntax that looks like ordinary code, and adds the REPL, metaprograms that run on every program, and certificates in the binary.

### Lean 4

Lean is a theorem prover that is also a fast programming language, with a small trusted kernel, the strongest metaprogramming of any language here and Mathlib behind it. Proofs in Lean are mostly written, with tactics and increasingly strong automation. Pia proves goals without being asked, which is less expressive and needs no proof writing for the overflow, bounds and contract goals that make up most of a program. Pia's `@by` tactics borrow the idea, as metaprograms that write proof steps.

### Idris 2

Idris makes types first-class and proofs programs, with quantitative types to track how often a value is used, and an interactive editor that fills holes and splits cases. Pia also treats types as values, under one `let` ([ADR 0002](adr/0002-single-let-binding-form.md)), but checks contracts with a solver instead of type-level proofs, and compiles to native code without a garbage collector.

### ATS

ATS combines dependent and linear types and compiles to C with no garbage collector, so it can prove low-level code safe at no run-time cost. That goal is Pia's too. ATS asks for proofs as terms and has a famously steep learning curve; Pia tries to reach the same place with contracts, a solver and counterexamples.

### SPARK

SPARK is Pia's nearest neighbour in spirit, and the one with the longest industrial record. It proves the absence of run-time errors (overflow, range, index and division checks) and functional contracts in a subset of Ada, compiles to native code with no garbage collector, and has an ownership model for pointers. Pia differs in syntax (ML instead of Ada), in proving as part of compiling instead of in a separate GNATprove run, in using one solver with interval analysis in front instead of several through Why3, and in metaprogramming, the REPL, the MCP server and certificates, none of which SPARK has. SPARK has tool qualification for certified software, which Pia is a long way from.

### Liquid Haskell

Liquid Haskell adds refinement types such as `{v:Int | v > 0}` to Haskell and checks them with Z3, inferring many refinements by itself. Pia's range types, such as `int{0..255}`, and `where` refinements on record fields are the same idea. Liquid Haskell keeps Haskell's laziness, garbage collector and ecosystem; Pia is strict, has no GC, and makes machine overflow a goal.

### Rust with Kani, Prusti, Verus or Creusot

Rust already proves memory safety with its borrow checker, and these tools prove more on top: Kani by bounded model checking, Prusti, Verus and Creusot by contracts and deductive proof. Verus is the most like Pia, with Z3, contracts and ghost code in a Rust subset. The difference is that in Rust the verifier is a separate tool over a language that was not designed for it, so arithmetic overflow is a debug-build panic or a release-build wrap unless a tool proves otherwise. Pia designs the language around the proofs: overflow is a compile error by default, and contracts are part of every interface a module exports.

### Why3

Why3 is a platform more than a language: WhyML programs and goals go to whichever provers can discharge them, and proofs can be finished by hand in Coq or Isabelle. SPARK and Creusot are built on it. Pia is a language with one compiler and one solver, which keeps the loop from code to counterexample short, at the cost of Why3's breadth.

### Others

Frama-C with ACSL proves annotated C, VeriFast proves C and Java with separation logic, and Coq (now Rocq) and Isabelle prove programs that are then extracted to code. Each takes an existing language or a proof assistant as its starting point. Pia starts from the other end: a language where every program is a set of goals, and the compiler's job is to prove them before it emits anything.

## Which to choose

- To prove mathematics, or properties that need dependent types, use Lean, F\*, Idris or Coq.
- To ship certified safety-critical software today, use SPARK.
- To prove an algorithm and ship it on a managed runtime, use Dafny.
- To add proofs to an existing Rust code base, use Kani or Verus.
- To try a language where machine-level code is proved as it is compiled, interactively and with an agent in the loop, try Pia: start with [Getting started](getting-started.md) and [the REPL](repl.md).
