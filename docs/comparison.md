# Pia and other verified languages

Pia is not the first language to prove programs correct, and it borrows from most of the ones on this page. This page says, for each of the closest languages and tools, what they share with Pia, where Pia differs, and where they are ahead. It tries to be specific and fair: every one of them is more mature than Pia, which has not reached a 0.1 release ([status](status.md)).

## In one table

| | How goals are proved | Default integers | Compiles to | Memory | Metaprogramming | Interactive loop |
| --- | --- | --- | --- | --- | --- | --- |
| **Pia** | Interval analysis, then Z3, automatically; lemmas and `@by` tactics when that is not enough | Machine integers, overflow is a goal | Native code through MLIR and LLVM | No GC; explicit, fallible allocators | `let meta` from day one; generated code is proved like hand-written code | `pia repl` proves every cell; `pia mcp` serves it to agents | Library theories: sorts, abstract functions and axioms with triggers, with a sealed model that proves the axioms; metaprograms can write them |
| **Dafny** | Boogie, then Z3, automatically, with hints and lemmas | Unbounded `int`; machine types by `newtype` | C#, Java, JavaScript, Go, Python | Garbage-collected targets | None | IDE that verifies as you type | Bodiless functions and `{:axiom}` lemmas; abstract modules that a refinement can prove |
| **F\*** | Z3 plus tactics (Meta-F\*), over dependent types and effects | Unbounded `int`; machine integer libraries | OCaml, F#; C through Low\* and KaRaMeL | GC, or manual in Low\* | Meta-F\* | Incremental checking in the editor | `assume val` and lemmas with `SMTPat` triggers; tactics |
| **Lean 4** | Tactics and automation (`simp`, `omega`, `grind`), checked by a small kernel | Unbounded `Nat`/`Int`; `UInt8` and friends wrap | C, with reference counting | Reference counting | Hygienic macros and elaborators, very strong | Infoview and `#eval` | `simp` sets and tactics written in Lean; definitions rather than axioms |
| **Idris 2** | Proofs as programs, written by hand; totality checking | Unbounded `Nat`/`Integer` | Chez Scheme and others | GC | Elaborator reflection | REPL and interactive editing with holes | Definitions and proofs; no solver to extend |
| **ATS** | Proofs as terms, plus a constraint solver for static indices | Indexed integers | C | No GC needed: linear types | Templates | None to speak of | Axioms as `praxi`, taken on trust |
| **SPARK** (Ada) | GNATprove, through Why3, to Alt-Ergo, CVC5 and Z3 | Machine integers, overflow is a check to prove | Native code through GNAT | No GC; ownership for pointers | Ada generics | IDE; no REPL | Lemma libraries and ghost models; axioms through Why3 |
| **Liquid Haskell** | Refinement types checked by Z3, with refinements inferred | Haskell's `Int` and `Integer` | Native code through GHC | GC | Template Haskell | GHCi, but proofs run in the plugin | Measures and `assume` refinements |
| **Rust verifiers** (Kani, Prusti, Verus, Creusot) | Bounded model checking (Kani, through CBMC) or deductive proof (Prusti through Viper, Verus through Z3, Creusot through Why3) | Machine integers; overflow panics in debug builds, wraps in release | Native code through rustc and LLVM | No GC; the borrow checker | Rust macros, which the verifiers see expanded | None; a separate tool run | Verus: broadcast lemmas with triggers; Kani: none |
| **Why3** | Many provers (Alt-Ergo, CVC5, Z3, Coq, Isabelle) over WhyML | Unbounded, with machine-integer libraries | Extraction to OCaml and C | Depends on the extraction | None | Proof sessions in its IDE | Theories of types, functions and axioms, cloned and realised in Coq or Isabelle; drivers map them to prover built-ins |

The table is a summary. Each tool has more options than one cell can hold, and the sections below say what matters.

Three more features set Pia apart in combination, though each has close relatives:

| | Teaching the prover a domain | Types as values | Generic constraints and their laws |
| --- | --- | --- | --- |
| **Pia** | Library theories: sorts, abstract functions and axioms with triggers, with a sealed model that proves the axioms; metaprograms can write them | Yes, at compile time: `let` binds types, and a generic type is a function that returns one | Concepts, which are metaprograms, with laws that Z3 proves for each instance; adapters; a generic body is proved once against its concepts |
| **Dafny** | Bodiless functions and `{:axiom}` lemmas; abstract modules that a refinement can prove | No | Type characteristics and traits; a trait's lemmas must be proved by each class |
| **F\*** | `assume val` and lemmas with `SMTPat` triggers; tactics | Yes, by dependent types | Type classes whose instances can carry proofs |
| **Lean 4** | `simp` sets and tactics written in Lean; definitions rather than axioms | Yes, by dependent types | Type classes with law fields (`LawfulBEq`, Mathlib's hierarchy), proved by each instance's author |
| **Idris 2** | Definitions and proofs; no solver to extend | Yes, by dependent types | Interfaces; laws as separate interfaces proved by hand |
| **ATS** | Axioms as `praxi`, taken on trust | No; static indices on types | Templates |
| **SPARK** (Ada) | Lemma libraries and ghost models; axioms through Why3 | No | Ada generics, proved instance by instance |
| **Liquid Haskell** | Measures and `assume` refinements | No | Type classes; laws stated and proved by hand with refinement reflection |
| **Rust verifiers** | Verus: broadcast lemmas with triggers; Kani: none | No | Traits; in Verus, specs on trait methods that each impl must meet |
| **Why3** | Theories of types, functions and axioms, cloned and realised in Coq or Isabelle; drivers map them to prover built-ins | No | Cloning a module turns its axioms into goals for the instance |

## What sets Pia apart

These are the choices that, taken together, no other language on this page makes.

- **Proving is compiling.** There is no separate verifier to run, and no mode where contracts are comments. `piac` proves every goal and refuses to compile while one fails or is unproved, unless `--allow-unproved` accepts it ([ADR 0004](adr/0004-strongest-guarantee-by-default.md)). Dafny comes closest: it verifies before it compiles by default, and it can be told not to.
- **The strongest guarantee is the default, on machine integers.** A `u8` is a byte, and `a + b` on two of them raises a goal that it does not overflow. Wrapping, saturating and trapping arithmetic exist, and each is something you ask for ([the tour](tour.md)). SPARK shares this; Dafny, Lean, Idris and F\* default to unbounded mathematical integers, which is easier to prove and further from the machine.
- **Cheap reasoning first.** Interval analysis settles the easy goals before Z3 sees them, and a goal Z3 refutes comes back as a counterexample: concrete inputs that break the code ([how verification works](verification.md)).
- **Built on MLIR.** Goals live in Pia's own MLIR dialects, next to the code they are about, and the code goes through LLVM to native instructions with every proved check erased. A proved index has no bounds check, and the facts the proofs establish are planned to drive vectorisation ([ADR 0011](adr/0011-mlir-and-z3-implementation.md), [ADR 0013](adr/0013-auto-vectorisation.md)).
- **Metaprogramming is part of the language, and its output is proved.** Operators are metaprograms in the prelude, `@derive` writes functions, and tactics are metaprograms that write proof steps. Whatever a metaprogram generates is verified like code you wrote ([metaprograms](meta.md)). Lean's macros and elaborators are at least as strong; Dafny, SPARK and Why3 have none.
- **Libraries teach the solver new domains, and prove what they teach.** A theory is an ordinary library module: sorts, functions with no body, and axioms with the triggers Z3 should use. A model gives each sort a type and each function a body, proves every axiom as a lemma, and is then sealed, so clients prove from the axioms alone and cannot be misled by a theory that contradicts itself. A theory with no model must be imported with `trusting`, and `piac --trust-report` lists every axiom a build relied on. Theories can be written by metaprograms, and Pia describes its own memory model, allocators and targets this way ([theories](theories.md), [ADR 0036](adr/0036-library-theories.md), [ADR 0049](adr/0049-targets-are-theories.md)). [Theories compared](#theories-compared) says which other tools come close.
- **Types are values, and concepts carry laws that are proved.** One `let` binds functions, values and types alike, and a generic type is a compile-time function that returns a type ([ADR 0002](adr/0002-single-let-binding-form.md)). A constraint on a type parameter is a concept: a metaprogram that checks what a type provides, in the spirit of C++ concepts or type traits, and states laws, such as reflexive equality, that Z3 proves for every type that meets it. Generic bodies are proved once against their concepts ([ADR 0009](adr/0009-generics-concepts-adapters.md), [ADR 0034](adr/0034-concepts-and-overload-resolution.md), [ADR 0043](adr/0043-generic-definitions-proved-once.md)). [Types and concepts compared](#types-and-concepts-compared) says where each idea comes from.
- **Proofs travel with the binary.** Each object carries a certificate of the interfaces it provides and requires, and a library whose interface changed cannot bind to a program that was proved against the old one, because the witness symbols the loader must bind are missing ([shared libraries and certificates](abi.md)). Most verifiers stop at the source: once compiled, nothing records what was proved.
- **A verified REPL, and an MCP server for agents.** `pia repl` proves every cell before it runs, refuses a redefinition that would break a caller, and swaps proved code into running tasks ([the REPL](repl.md)). `pia mcp` serves that session to an agent, and teaches it the language: a primer when it connects, `:help` topics, hints on failed cells and what each proof cost. Lean and Idris have excellent interactive loops, but they check code and run it as separate steps; Pia's REPL never runs a cell it has not proved.
- **No garbage collector, ever.** Allocators are explicit and every allocation can fail ([ADR 0026](adr/0026-memory-manager.md)), as in SPARK, ATS and Rust.

## Feature by feature

The rest of the language, one feature per row, with what exists today and where the idea comes from. "Built" means `piac` compiles and proves it now; "designed" means an accepted ADR that is not built yet.

| Feature | In Pia | State | Closest elsewhere |
| --- | --- | --- | --- |
| Errors and cleanup | Closed error sets, `e?` and scoped `handle` arms, each arm proved at each `?` that reaches it; `defer` runs on every exit, and cleanup never replaces the error in flight ([ADR 0028](adr/0028-error-propagation-and-cleanup.md)) | Built | Zig's error sets, `try` and `errdefer` are the nearest; Rust's `?` and `Drop`; Swift's typed `throws`. None of them proves the handlers |
| Ownership | `borrowed`, `moved`, `in`/`out`/`inout` parameters, `@linear` types that must be consumed, `drop`, and borrows that end at their last use ([ADR 0005](adr/0005-parameter-modifiers.md), [ADR 0042](adr/0042-lifetimes-liveness-and-escape-analysis.md)) | Built in part: regions on types and escape analysis are designed | Rust's ownership (affine, with `Drop`); linear types in ATS, Linear Haskell and Austral; Mojo's as-soon-as-possible drop |
| Memory | No GC and no `new`: explicit allocators, every allocation can fail, arenas on the stack, and allocator behaviour stated as the theory `Alloc`, which each allocator proves it refines ([ADR 0026](adr/0026-memory-manager.md), [ADR 0041](adr/0041-allocator-semantics-as-a-theory.md)) | Built | Zig's explicit, fallible allocators; Rust's `try_reserve`. Neither proves what an allocator promises |
| Metaprogramming | `let meta` functions with quotes and splices, expanded to a fixed point with a cycle limit; hygiene by forbidding shadowing outright; operators, derives and tactics are all metaprograms ([ADR 0007](adr/0007-metaprogramming-fixed-point-expansion.md), [ADR 0022](adr/0022-metaprogram-hygiene.md)) | Built | Lisp and Racket macros, Lean's macros and elaborators, Zig's `comptime`. Zig also forbids shadowing |
| Specification state | Spec-only types (`int`, `real`) and `spec` locals and buffers, which proofs use and codegen erases; no `ghost` keyword ([ADR 0058](adr/0058-spec-buffers.md)) | Built: fixed-size `spec` buffers first | Ghost code in Dafny, Verus, SPARK and Why3 |
| Cost bounds | `costs c <= e` in a contract bounds the work a function does on a named counter, proved by Z3; asymptotic and closed-form facts go to Lean ([ADR 0062](adr/0062-cost-bounds-in-contracts.md), [ADR 0061](adr/0061-lean-proved-facts.md)) | Designed | Research tools: RAML's resource analysis, time credits in Iris and CFML. No mainstream verifier proves complexity |
| Facts Z3 cannot prove | A goal Z3 cannot decide, such as a nonlinear or inductive fact, can be proved in Lean and used by Pia ([ADR 0061](adr/0061-lean-proved-facts.md)) | Designed | Why3 and SPARK send such goals to Coq or Isabelle; F\* has tactics |
| Certificates | Each object carries the interfaces it provides and requires, as hashes and witness symbols, so a stale library fails to bind; `pia-cert check` runs in every `pia_library` build ([ADR 0024](adr/0024-published-proof-certificates.md)) | Built: audit and trusted-item reports are designed | Proof-carrying code (research); OCaml's interface digests, which check identity without contracts |
| Parallel loops | `spread` runs iterations in parallel, and the compiler proves from ownership footprints that no two iterations touch the same data ([ADR 0060](adr/0060-spread-v0-ownership-and-runtime.md)) | Built: v0, on the CPU | Rust's `Send`/`Sync` and Rayon, checked by types; OpenMP, not checked. Verus and Iris prove concurrent code by hand |
| Concurrency | Stackless coroutines, race freedom and lock-order deadlock freedom by proof, channel protocols checked by Z3 ([ADR 0027](adr/0027-coroutines-and-race-freedom.md), [ADR 0053](adr/0053-protocols-checked-by-z3.md)); the RC11 memory model as a theory with a litmus battery ([ADR 0052](adr/0052-atomics.md)) | Designed; the memory model is built | Session types; TLA+ and model checkers for protocols; Iris for proofs about atomics |
| Tests from contracts | Metaprograms generate test cases from contracts, types and theories; each case goes to the verifier first, and only the cases it cannot decide are run ([ADR 0056](adr/0056-tests-generated-from-contracts-and-theories.md)) | Built in part: the metaprogram builtins; generators next | QuickCheck and Hypothesis, which run every case; Dafny's test generation |
| Floating point | Strict IEEE by default, three explicit ways to allow reassociation, kernels proved against `real` theories, and no trusted libm: every maths function written in Pia with its error bound in its contract ([ADR 0012](adr/0012-floating-point-reassociation.md), [ADR 0038](adr/0038-float-kernels-against-real-theories.md)) | `f32` and `f64` are built, strict IEEE and bit for bit with C, with `@fp(reassoc, contract)` to license vectorised reductions and FMAs per function; proofs see exact IEEE order and conversion goals, while real-valued error bounds are designed, not built | SPARK and Frama-C prove float code through Why3; Gappa and Flocq prove error bounds in Coq |
| Integer types | Range types `int{0..255}`, `min u8` and `max u32` folded to literals, and digit separators such as `100'000` ([ADR 0059](adr/0059-digit-separators-and-type-bounds.md)) | Built | Ada's range types and `'First`/`'Last`; C++14's `'` separators |
| Literate programs | Comments are syntax that metaprograms can read, and a `.pia.md` file is Markdown whose `pia` blocks are the program; the demos on this site are proved that way ([ADR 0029](adr/0029-comments-as-syntax-and-literate-pia.md)) | Built | Literate Haskell, Agda's literate Markdown, Lean's doc-gen |
| Tooling | A language server, the verified REPL, an MCP server that teaches the language and reports proof costs, and agent skills whose examples are proved ([the REPL](repl.md), [agent skills](agents.md)) | Built | Lean's and Dafny's language servers are more mature; MCP servers for Lean exist as community projects, while Pia's is part of the toolchain |

## Where the others are ahead

Pia's choices have costs, and the other languages have years of work Pia does not.

- **Maturity.** Dafny, SPARK, F\*, Lean and Liquid Haskell have been used for real systems for a decade or more. SPARK is used in avionics and security work, F\* produced the HACL\* cryptography in Firefox and the Linux kernel, and Lean has Mathlib. Pia compiles a subset today, for one target (arm64 macOS); float error bounds, compiling recursive types and much of the concurrency design are not built yet ([status](status.md#known-limitations)).
- **Expressiveness.** Lean, F\* and Idris have dependent types, so a type can say almost anything, and a proof can be as long as it needs to be. Pia's goals are first-order formulas that Z3 decides or gives up on. A property that needs induction needs a lemma, and some nonlinear or deeply quantified goals will not prove automatically at all. Handing those to Lean is designed ([ADR 0061](adr/0061-lean-proved-facts.md)) but not built.
- **The trusted base.** Lean checks every proof with a small kernel, so a bug in a tactic cannot prove something false. Pia trusts Z3, the way the verifier encodes goals for it, and the compiler. Its certificates record which interfaces were proved, not proofs that someone else can check, and the planned `pia-cert audit` re-checks obligations with your own Z3, not the machine code ([trust model](abi.md#trust-model)).
- **Prover choice.** Why3 and SPARK send a goal to several provers and keep the one that succeeds. Pia uses Z3 alone, with solver strategies (`@solver`) as the escape hatch.
- **Bounded model checking.** Kani checks Rust code bit-precisely, unsafe code included, up to a bound, with no invariants to write. Pia needs a loop invariant for each loop, and has nothing like Kani for code that is not Pia.
- **Ecosystems.** Rust, Haskell and Ada have libraries for everything. Pia's standard library is being written in Pia, over a small POSIX core ([standard library](stdlib.md), [the C++ standard library in Pia](cpp-std.md)).

## Types and concepts compared

Neither idea is new on its own, and Pia's take on each is narrower than the strongest version elsewhere.

- **First-class types.** Lean, Idris, F\*, Agda and Coq have dependent types, in which types are values in the fullest sense: a type can depend on a run-time value, and a function can return a type that is used to check the rest of the program. Pia's types are values at compile time only, as in Zig, whose generics are also functions from types to types. Pia does not have dependent types; what a dependent type would say, Pia says with a range type, a `where` refinement or a contract, and Z3 proves it.
- **Concepts.** C++20 concepts check that a type provides the operations a template uses, and Pia's concepts check the same kind of thing, with a metaprogram instead of a `requires` expression. C++ concepts cannot check meaning: a concept's semantic requirements, such as that `==` is an equivalence, are documentation, and the axioms proposed for C++0x concepts were dropped. Haskell's and Rust's type classes and traits are in the same position. A Pia concept states such requirements as laws, and each instance proves them, automatically, before it can be used; an instance cannot assume them.
- **Laws elsewhere.** Lean, F\* and Idris can put proofs in a type class, and Mathlib's algebraic hierarchy is built that way: a stronger version of the same idea, since a law can be any theorem, but each instance's author writes its proofs. Dafny traits can declare lemmas that each class proves, and Why3 turns a cloned module's axioms into goals. Pia's contribution is to make lawful concepts the ordinary way to write generics, with the laws proved by Z3 for each instance and adapters for types that meet a concept only in their own way, such as `f32` equality, which fails reflexivity at NaN ([language design](design.md)).

## Theories compared

Every verifier on this page lets a library add knowledge that the prover does not have built in. What differs is whether that knowledge is checked, and who can add it.

- **Why3 is the closest.** Its theories declare types, functions and axioms, are instantiated by cloning, and can be *realised* in Coq or Isabelle, which proves the axioms, much as a Pia model does. Its drivers map a theory onto a prover's built-in theories. Pia's theories descend from these. The differences are that a Pia model is written in Pia and proved by the same solver, that sealing is enforced, so a client cannot see past the axioms to the model, and that theories can be generated by metaprograms.
- **F\* and Verus** let a lemma carry a trigger (`SMTPat` in F\*, `broadcast` lemmas in Verus), so the solver applies it on its own wherever a matching term appears. That is the same mechanism as an axiom's trigger in a Pia theory, except that the fact is proved, not assumed. F\* also has `assume val` for facts taken on trust, with no model to check them.
- **Dafny** has functions with no body and lemmas marked `{:axiom}`, and abstract modules whose refinements must prove the abstract lemmas. That is close to a Pia theory with a model, though nothing stops a client from depending on an axiom that no refinement proves, and there is no report of which axioms a program used.
- **Lean** needs no axioms at all for most domains: a domain is a set of definitions, facts about it are theorems, and `simp` sets and custom tactics, written in Lean, are how a library teaches automation about it. That is more general than Pia's theories and checked by the kernel; the cost is that the automation is a tactic search, not an SMT query that a trigger steers.
- **SPARK** has lemma libraries and ghost models for its functional containers, and can pass external axiomatisations through to Why3. **Liquid Haskell** has measures and `assume`d refinements. **ATS** has `praxi`, axioms taken on trust. **Idris** and **Kani** have no solver theory to extend.

What Pia adds is the combination: a theory is a library like any other, a model proves it consistent and is sealed, trust is explicit and reported, `--check-vacuity` catches a goal proved only because trusted axioms contradict each other, and metaprograms can build theories and the tactics that use them.

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
