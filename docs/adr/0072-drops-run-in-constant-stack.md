# 72. Drops run in bounded stack: recursive values are dropped by pointer reversal, and nothing else can nest without bound

Date: 2026-11-27

Status: Proposed

## Context

Dean (2026-11-27): "I want to think about the recursive drop case where we can get stack overflows. Independent of whether or not there's recursion actually happening, for deep enough drop calls we need to be mindful of the stack usage. We should figure out whether we need to do some sort of mark-sweep instead of the naive calls to drop recursively."

A naive drop calls the drop of each field, which calls the drop of each of its fields, and so on, one stack frame per level of nesting. How deep that goes depends on what the value is:

- A value of a type that is not recursive nests as deeply as its type does, and no deeper. A `box (box (box u8))` is three levels, whatever is in it.
- A value of a recursive type ([ADR 0047](0047-recursive-sum-types-and-shared-references.md)) nests as deeply as the value is built: a list a million long is a million levels.
- A `box c` ([ADR 0046](0046-box-over-a-type-or-a-concept.md)) hides its type. If a type that meets `c` holds a `box c`, as a node of a heterogeneous list does, then `box c` is recursive through the concept, even though no `let rec` says so.
- A `ref t` drops its value when its last strong reference goes (ADR 0047, section 5), so a chain of last references is a recursive drop too.

ADR 0047's section 4 already says that the generated drop of a recursive type runs in constant stack, by looping along one child and threading the others onto a worklist kept in the memory of the nodes being freed. That leaves open what happens when a freed node has no room for the list, the order in which fields are dropped, a recursive type with a `drop` written by hand, recursion through `box c` and `ref`, and the stack used by drops that do not recurse.

### Prior art

- **Rust** drops recursively, so dropping a long `Box`-linked list overflows the stack; the usual fix is a hand-written `Drop` that loops with `take()`, and a tree needs an explicit stack.
- **C++**'s `unique_ptr` chains have the same problem.
- **Garbage collectors** mark with an explicit stack or by **Deutsch–Schorr–Waite pointer reversal** (1967), which walks a graph in constant extra space by turning each pointer it follows around to point back to where it came from, restoring it on the way out. A few bits per node record which child comes next.
- **Swift** and **Koka** release counted references iteratively where the compiler can see the chain.

## Decision

### 1. What a drop may nest through

The compiler computes, for every type, whether its drop can nest without bound. It can when the type reaches itself through an indirection: a `let rec` type through `box`, `vec` or `ref` (ADR 0047), or a type that meets a concept `c` and holds, directly or through its fields, a `box c` or a `vec (box c)`. Every other type has a fixed drop depth, known when it is compiled.

### 2. Recursive values are dropped by pointer reversal

The generated drop of a type that can nest without bound does not recurse. It walks the value by pointer reversal:

- To descend into a recursive child, it turns that child's pointer in the parent to point back to the parent's parent, and records which child it took in the low bits of that pointer, which are free because every slot is aligned to at least four bytes. A node with more children than those bits can count keeps its count in its own memory, whose other fields have already been dropped.
- When a node's children are all done, it drops the node's remaining fields, frees its slot, and climbs back up through the reversed pointer.
- One child, the last, is followed by a loop rather than a reversal, so a list, the common case, needs no reversal at all. This is ADR 0047's loop.

It uses a fixed number of stack slots and allocates nothing, which matters because every allocation in Pia is fallible ([ADR 0026](0026-memory-manager.md)) and a drop cannot fail. This replaces ADR 0047's worklist, which needed a freed node to have room for a link.

### 3. Fields are dropped in the order the naive drop would use

The walk visits children in declaration order, depth first, and drops a node's own fields after its children, as the recursive drop would. So a value whose fields close files or release locks does so in the same order however deep it is, and a program can rely on that order. Freeing a slot happens after everything in it is dropped.

### 4. A hand-written `drop` of a recursive type

A recursive type may still have its own `drop` (#85). It sees the node's fields other than the recursive ones, which the compiler drops after it by the walk above. So a hand-written drop cannot call a drop on a recursive child and recurse by accident, and it cannot reach the children after they have gone. A `drop` that needs to look at its children first does so through a borrowed read, which costs no stack beyond its own loop.

### 5. Through `box c` and `ref`

- **`box c`.** When a type that meets `c` can hold a `box c` (section 1), its table entry for drop (ADR 0071, section 6) is a step, not a full drop: it drops the object's fields that are not boxes of `c`, and hands each `box c` it finds back to the caller instead of dropping it. Dropping a `box c` is a loop over those steps, with the boxes waiting to be dropped threaded through the freed slots by pointer reversal, as in section 2. The table entry stays out of reach of Pia (ADR 0071), so this protocol is the compiler's alone.
- **`ref t`.** Releasing the last strong reference to a value that holds `ref t` fields releases those references in the same walk, so a chain of last references unwinds in constant stack, as Swift and Koka do where they can see the chain.

### 6. Every other drop has a known depth

A type that cannot nest without bound has a drop depth the compiler knows, and with it the stack its drop uses: the sum of the frames of the drops along its deepest path, which codegen measures from LLVM's frame sizes once the drops are compiled. The compiler reports the deepest drop in a function with `--verify-stats`.

The limit comes from the target (Dean, 2026-11-27), not from a fixed number of levels. The `Pia.Target` theory ([ADR 0049](0049-targets-are-theories.md)) gains `task_stack_bytes`, the smallest stack a Pia task runs on for that target: the stack of a thread the runtime starts, since the main thread's is larger. On arm64 macOS that is 512 KiB, the default for a thread other than the main one; on x86_64 Linux it is 8 MiB, the default `RLIMIT_STACK` that glibc gives new threads. A drop whose stack is more than an eighth of `task_stack_bytes` (64 KiB on macOS, 1 MiB on Linux) is a lint, `deep_drop`, which names the type and the path and suggests a `box` to flatten it. `--drop-stack=<bytes>` sets another budget, for a program that runs on smaller stacks or sets its own. With sections 2 to 5, no drop in a Pia program uses stack that grows with its data, so this budget is about a type's shape alone.

### 7. Proofs

What the verifier sees does not change. A drop is still its type's `drop` contract, and each node is still dropped exactly once (ADR 0047, section 3). The walk is the compiler's lowering of that drop, proved once in the compiler's test suite for each shape of type (one child, several children, `box c`, `ref`) against the naive recursive drop: the same calls, in the same order, on random values, under the sanitizers ([ADR 0025](0025-sanitizers.md)).

## Implementation order

Each step is a PR with tests in `tests/codegen` run from C, and the `pia-language` skill updated when the lint lands.

1. **Drop depth.** Which types can nest without bound (section 1), the stack of every other drop in `--verify-stats`, `task_stack_bytes` in `Pia.Target`'s two models, and the `deep_drop` lint against it.
2. **Lists.** The loop along the last child for `let rec` types with one recursive child, with a test that drops a list of a million nodes in a thread with a 64 KiB stack.
3. **Trees.** Pointer reversal for several children, and the order of section 3, with a test that drops a left-leaning tree of a million nodes and checks the order of the drops it runs.
4. **Hand-written drops** of recursive types (section 4).
5. **`box c` and `ref`** (section 5), after ADR 0071's tables: a heterogeneous list of `box Shape` a million long, and a chain of last references.

## Consequences

- No drop overflows the stack because a value is large, and a drop allocates nothing, so dropping never fails.
- Drops of recursive values run in the order a programmer would expect from the recursive definition, so moving to the walk changes no program's behaviour.
- A hand-written drop of a recursive type sees less than it would in Rust or C++: its recursive children are the compiler's to drop.
- Pointer reversal writes to the nodes it is dropping. That is safe because they are owned uniquely and about to be freed, but it means a drop cannot run while another task borrows the value, which ADR 0042's loan rules already forbid.
- The walk costs a little more per node than the naive recursion for trees. Lists cost the same.

## Questions for Dean

1. **The budget.** Is an eighth of the target's task stack the right share for one drop, and should exceeding it be a lint (recommended) or an error? *Dean, 2026-11-27: take the default from the target's stack limits.*
