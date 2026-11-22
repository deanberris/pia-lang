# 40. The C++23 standard library, mapped onto Pia and proved

Date: 2026-11-22

Status: Proposed

## Context

Dean asked for the C++23 standard library in Pia, now that Pia has generics, concepts, slices, `result` with `?`, `defer` and `Drop`, `@linear`, borrows, `with_arena` and a proved generic `vec` over a bump allocator. [ADR 0023](0023-minimal-core-self-hosted-stdlib.md) already decided that the library is written in Pia over a minimal core, and [docs/stdlib.md](../stdlib.md) lays it out in layers (`Pia.Core`, `Pia.Sys`, `Pia.Mem`, `Pia.Io`, `Pia.Math`, `Pia.Par`). What it does not say is how much of what a C++ programmer expects from `std` Pia provides, under which names, and in what order.

C++23 has about a hundred headers. Some translate directly (`<bit>`, `<algorithm>`, `<charconv>`). Some exist because of a C++ mechanism that Pia replaces (`<exception>`, `<iterator>`, `<memory>`'s `std::allocator`, `<type_traits>`). Some need things Pia does not have yet (floats, atomics, function values). And some are out of scope for reasons of principle (`<locale>`, wide characters, `<any>`).

A verified library also has to say more than C++'s does. The standard states preconditions in prose ("the behaviour is undefined if `[first, last)` is not sorted"), and results as "Effects:" and "Returns:" clauses. In Pia, each of those is a contract the compiler proves, so the library cannot be a transliteration: every function needs a specification precise enough to prove, which often needs a spec function the standard never names (`sorted`, `count`, `permutation`).

Prior art: Rust's `core`, `alloc` and `std` give the same capabilities as C++'s library under different idioms (slices for iterator pairs, `Result` for exceptions, traits for concepts). SPARK's formal containers and Ada's `Ada.Containers` show contracts written against a mathematical model. Dafny's and Verus's standard libraries (`vstd`) show which specifications are practical to prove. Zig's `std` shows a library where every allocating function takes an allocator.

## Decision

### 1. Capability parity, not API parity

Pia provides what the C++23 library lets a program do, in Pia's idioms, not C++'s names and signatures. A C++ programmer finds each `std` entity through [docs/cpp-std.md](../cpp-std.md), a header-by-header map that says, for each header, which Pia module provides it, whether it is direct, replaced by a Pia idiom, deferred (and on what), or out of scope (and why). The map is updated by every library PR, so it is also the status page.

Each library function's doc comment names the C++ entity it corresponds to, as `(** C++: std::lower_bound *)`, so the language server, search and the map agree.

Names follow Pia's style: snake case, single words where they are clear (`find`, `count`, `fill`, `rotate`), the C++ name where it is the established term (`lower_bound`, `popcount`, `gcd`, `iota`), and no `std::` prefixes, `_t` suffixes or `_if` variants (see section 6).

### 2. C++'s prose becomes proved contracts

- **Every precondition is a `requires`.** What is undefined behaviour in C++ is a proof goal at the call in Pia: an unsorted range passed to `lower_bound`, an index past the end, a `pop` on an empty heap, a shift by the width or more, `midpoint` of nothing, `gcd` overflowing. None of these has a run-time check, because none can happen in a proved program.
- **Every "Returns:", "Effects:" and "Postconditions:" clause is an `ensures`**, written with spec functions in the module (`sorted`, `count`, `permutation`, `is_heap`, `prefix`). `sort` promises a sorted permutation of its input, `lower_bound` the first index whose element is not less than the key, and `to_chars` a string that `from_chars` reads back to the same value.
- **Where C++ leaves something unspecified, Pia picks one answer and states it**: which of equal elements `min_element` returns, the order of a `partition`'s halves, the contents of a slice after `remove`. Code may rely on what the contract says, and on nothing else.
- **Complexity clauses are documented, not proved.** "At most `log2(n) + 1` comparisons" goes in the doc comment. Pia has no cost proofs yet (see the gaps below), so the library is tested against them with benchmarks instead.
- **Laws a C++ concept states but cannot check are concept laws.** `Ord`'s strict weak order (irreflexive, transitive, and transitive incomparability), `Eq`'s equivalence and `Hash`'s agreement with `Eq` are lemmas proved for every instance ([ADR 0034](0034-concepts-and-overload-resolution.md)), so a `sort` over a type whose `less` is not a strict weak order is rejected where it is instantiated, rather than misbehaving at run time.

### 3. No exceptions: closed error sets

- A C++ function that throws becomes one that returns `result t e`, where `e` is a closed variant naming exactly the errors that can happen ([ADR 0028](0028-error-propagation-and-cleanup.md)). There is no `std::exception` hierarchy, no `what()` and no `noexcept`: a function with no error set cannot fail.
- `std::bad_alloc` is `OutOfMemory`, returned by every allocating call and handled at its call site ([ADR 0026](0026-memory-manager.md)). No container function allocates without saying so in its type.
- C++'s pairs of checked and unchecked accessors collapse. `v[i]` and `v.at(i)` are both `v.[i]` with the bound proved. An accessor that returns `option` exists only where the caller cannot be expected to prove the bound, such as a lookup by key.
- `std::errc` and `std::error_code` become the error variants of the module that raises them; `Pia.Sys` decodes `errno` into its own variants ([ADR 0023](0023-minimal-core-self-hosted-stdlib.md)).

### 4. Allocators are explicit, and every container is a `pmr` container

- Every allocating function takes a `borrowed` allocator that meets `Allocator` ([ADR 0026](0026-memory-manager.md)). There is no `std::allocator` and no default global heap, so C++'s `std::pmr` is the only model, and `<memory_resource>`'s `monotonic_buffer_resource`, `unsynchronized_pool_resource` and `synchronized_pool_resource` are `Pia.Mem`'s `arena`, `pool` and `shared` allocators.
- `<scoped_allocator>` has nothing to do: a container's elements that allocate are given their allocator explicitly, and borrows ([ADR 0026](0026-memory-manager.md)) prove that none outlives it.
- `unique_ptr<T>` is a `@linear` or `Drop` box from an allocator. `shared_ptr` and `weak_ptr` are deferred: shared ownership needs a reference count whose last release frees, which needs atomics for the shared case, and a proof that cycles cannot leak, which needs recursive types.

The allocators, `vec` and the containers built on them (issue #72) are owned by the `Pia.Mem` work (#59, #71, #86, #88). This ADR maps C++'s containers onto that work and adds the ones #72 does not list, but does not change `Pia.Mem`'s design.

### 5. Iterators become slices and indices

- A pair of iterators `[first, last)` over contiguous storage is a slice `[t]`, and a sub-range is `xs.[a .. b]`. An output iterator is an `out` slice whose length is proved to be enough, so `copy`, `transform` and `set_union` cannot write past the end. A position is a `usize` index, and "an iterator to the found element, or `last`" is an index in `0 .. len xs`, with `len xs` meaning not found, so an index result composes with slicing as C++'s iterators do with ranges.
- `std::span` is the slice type itself, `std::array<T, N>` is `[T; N]`, and `std::string_view` is a `str` slice. None needs a library type.
- Node-based containers (`list`, `map`, `set`) expose a cursor type of their own, an index into their node pool, proved valid by the container's invariant, instead of a general iterator concept. Iterator categories, sentinels, `iterator_traits` and `<iterator>`'s adaptors have no Pia counterpart.
- Lazy views (`<ranges>`'s `views::filter`, `transform`, `zip`, `chunk`) wait for function values (see the gaps). The eager algorithms over slices come first.

### 6. Comparators and predicates come from concepts first

- Algorithms that compare use `Eq` and `Ord` instances found by argument-dependent lookup ([ADR 0034](0034-concepts-and-overload-resolution.md)), and hashing uses `Hash`. A different order is a different type: a record that wraps the value and has its own `less`, as Rust's `Reverse` does. This is the common case in C++ too, and it monomorphises and vectorises.
- `<compare>`'s `strong_ordering`, `weak_ordering` and `partial_ordering` are variants in `Pia.Core.Order`, with `compare` (the three-way comparison) derived from `less` and `same`, and `@derive(ord)` as a library metaprogram (#61).
- The `_if` algorithms (`find_if`, `count_if`, `remove_if`, `all_of`), `transform`, `sort` with a comparator, and `accumulate` with an operation need a predicate or an operation passed as a value. Pia cannot compile function values yet, so these wait for them (see the gaps). They will be the same functions with a function parameter, not a second family.

### 7. Text is UTF-8 bytes

- `str` is `[u8]` refined to valid UTF-8, and `string` is a `vec u8` with the same invariant ([docs/stdlib.md](../stdlib.md), `Pia.Io`). `char` in C++'s sense is `u8`, and a code point is `u32{0..0x10FFFF}` without the surrogates.
- There are no wide characters (`wchar_t`, `<cwctype>`, `wstring`), no `char8_t`/`char16_t`/`char32_t` string types and no locales (`<locale>`, `<clocale>`, `<codecvt>`). Classification is ASCII (`<cctype>`) in `Pia.Core.Ascii`; Unicode properties, normalisation and UTF-16 conversion for foreign APIs come later in `Pia.Text`, from tables generated by metaprograms.
- `std::format` and `std::print` are `Pia.Text.Format`: format strings are checked when the program is compiled, as C++20's are, by a metaprogram that reads the literal and the argument types. `std::formatter` specialisations are instances of a `Format` concept.

### 8. Type traits and concepts are metaprograms

`<type_traits>` and most of `<concepts>` exist because C++ templates cannot ask questions about types directly. In Pia, a metaprogram can ([ADR 0035](0035-substitution-failure-and-total-constraints.md)): `is_integral t` is a type `match`, `make_unsigned` is a type-level function, `enable_if` is a `where` clause, and `std::same_as`, `std::integral` and `std::totally_ordered` are concepts in `Pia.Core.Order` and `Pia.Core.Int`. `Pia.Core.Traits` collects the type-level metaprograms that turn out to be needed, rather than mirroring the header. `<typeinfo>`, `<typeindex>` and `<any>` have no counterpart: there is no run-time type information, and dynamic values are `dyn` ([ADR 0003](0003-static-typing-with-tagged-dyn.md)).

### 9. Tuples are a core type

Tuples are first-class types and values in the core, as arrays and records are, rather than a library type waiting for variadic generics (Dean, 2026-11-22). This needs a core change of its own, with its own ADR, before `<tuple>` is done; this section records what the library expects of it.

- **Values and types share one syntax.** `(a, b, c)` is a tuple value and, since types are values, `(u8, str, bool)` is its type: a tuple of types is a tuple type. `()` is the empty tuple, the same value as `unit`. There is no one-element tuple: `(x)` is `x` in parentheses.
- **Access is positional.** `t.0`, `t.1` and so on, checked when compiled, so an index out of range is a type error, not a proof goal. Patterns destructure: `match t with | (a, b) -> ...` and `let (a, b) = t in ...`; a pattern is told apart from a function literal `let (x) => ...` by the `=>`, as [grammar.md](../grammar.md) already plans.
- **A tuple is an anonymous record.** It has the same layout, ownership and modifier rules as a record whose fields are named `0`, `1`, ...: layout optimisation ([ADR 0030](0030-published-object-layouts.md)), struct-of-arrays buffers (`[(u32, f32)]` is one buffer per element), `moved` and `@linear` elements, borrows, and contracts that name `t.0`. Tuples of the same element types are the same type wherever they are written, which is what a named record is not.
- **Equality, order and hashing are structural.** `Eq`, `Ord` and `Hash` instances for a tuple come from its elements' instances, element by element and lexicographically, with the laws proved once for the generic definition (ADR 0043). This is C++'s `operator<=>` on `tuple`.
- **Tuple types are the type lists for variadic code.** A type parameter can stand for a tuple type, and a metaprogram walks it with a type `match` on `()` and on a head and tail, proved terminating by structural recursion as ADR 0035 requires. That is enough for `apply`, `tuple_cat`, `tuple_size`, `tuple_element`, `std::get` by type, and argument packs for `format` and `make_unique`, without a separate pack feature. `variant<Ts...>` stays a named variant for now: an anonymous sum type is a separate decision.
- **Foreign code** sees a tuple as the C struct of its elements, in the order the layout chooses and advertises in the ABI, as for records.

`std::pair` is a two-element tuple, `std::tie` is a tuple pattern, and structured bindings are `let (a, b) = ...`.

### 10. Maths is proved in Pia, never libm

`<cmath>`, `<numbers>`, `<complex>`, floating-point `<charconv>` and the floating-point distributions of `<random>` are `Pia.Math` and wait for floats (M11), with error bounds in their contracts ([ADR 0023](0023-minimal-core-self-hosted-stdlib.md), [ADR 0038](0038-float-kernels-against-real-theories.md)). Everything over integers comes first: `<bit>`, `<numeric>`, integer `<charconv>`, `<chrono>`'s integer durations and calendar, `<ratio>`, and `<random>`'s integer engines and `uniform_int_distribution`.

### 11. Module layout

The library is a tree of modules, one per file ([ADR 0039](0039-module-and-interface-syntax.md)), in `lib/`, named by path: `lib/Pia/Core/Bit.pia` holds `module Pia.Core.Bit`. Each module has a `pia_library` target in `lib/Pia/<Layer>/BUILD.bazel`, so it is proved on its own and its dependents build against its interface artifact.

| Module | C++23 headers | Needs |
| --- | --- | --- |
| `Pia.Core.Bit` | `<bit>`, `<bitset>` | the bit builtins below |
| `Pia.Core.Int` | `<numeric>`'s `gcd` `lcm` `midpoint`, `<utility>`'s `cmp_less` `in_range`, `<limits>`, `<climits>`, `<cstdint>`, `<cstdlib>`'s `abs` `div`, C++26's saturating arithmetic | available now |
| `Pia.Core.Order` | `<compare>`, `<concepts>`'s comparison concepts, `<utility>`'s `swap` `exchange` | available now |
| `Pia.Core.Option`, `Pia.Core.Result` | `<optional>`, `<expected>` (`<variant>` is core sum types) | available now; monadic operations wait for function values |
| `Pia.Core.Algo` (`Search`, `Modify`, `Sort`, `Heap`, `Set`, `Perm`) | `<algorithm>`, `<numeric>`'s `iota` `accumulate` `reduce` `partial_sum` `inner_product` `adjacent_difference` | available now for the comparison-based forms |
| `Pia.Core.Ascii`, `Pia.Core.Utf8`, `Pia.Core.Charconv` | `<cctype>`, `<cuchar>`, `<string_view>`, `<charconv>` for integers | available now |
| `Pia.Core.Hash` | `std::hash` | available now |
| `Pia.Core.Fixed` | C++26's `inplace_vector`, a ring buffer | value parameters in generic types |
| `Pia.Core.Rand` | `<random>`'s integer engines and integer distributions | available now |
| `Pia.Core.Ratio`, `Pia.Time` | `<ratio>`, `<chrono>`, `<ctime>` | integer durations and the civil calendar now; clocks need `Pia.Sys.Clock`; time zones need files |
| `Pia.Mem`, `Pia.Mem.*` | `<memory>`, `<memory_resource>`, `<new>`, `<vector>`, `<deque>`, `<list>`, `<forward_list>`, `<map>`, `<set>`, `<unordered_map>`, `<unordered_set>`, `<flat_map>`, `<flat_set>`, `<queue>`, `<stack>` | the allocators (#59, #71) and #72 |
| `Pia.Text`, `Pia.Text.Format` | `<string>`, `<format>`, `<print>` | `Pia.Mem.Vec`; `print` needs `Pia.Io` |
| `Pia.Io`, `Pia.Sys.Fs` | `<iostream>` and the stream headers, `<cstdio>`, `<filesystem>` | `Pia.Sys` (#57) |
| `Pia.Rt` | `<stacktrace>`, `<csignal>`, `<cassert>`'s `abort` | #58 |
| `Pia.Math` | `<cmath>`, `<numbers>`, `<complex>`, `<cfenv>`, `<stdfloat>` | floats (M11) |
| `Pia.Sync`, `Pia.Task`, `Pia.Chan` | `<atomic>`, `<thread>`, `<mutex>`, `<shared_mutex>`, `<condition_variable>`, `<semaphore>`, `<latch>`, `<barrier>`, `<future>`, `<stop_token>`, `<generator>`, `<execution>` | atomics and the concurrency runtime (M12, [ADR 0027](0027-coroutines-and-race-freedom.md)) |
| `Pia.Fn` | `<functional>` | function values |
| `Pia.Text.Regex` | `<regex>` | later: a linear-time automaton engine, so matching is proved to terminate |

Out of scope, with what replaces each: `<exception>` and `<stdexcept>` (error variants), `<typeinfo>`, `<typeindex>` and `<any>` (metaprograms and `dyn`), `<locale>`, `<clocale>`, `<codecvt>` and `<cwctype>` (UTF-8 only), `<valarray>` (`vec<T, k>` and `spread`), `<csetjmp>` (nothing), `<cstdarg>` (Pia has no C variadics, and calling a variadic C function is not supported), `<initializer_list>` (array literals), `<scoped_allocator>` (explicit allocators), `<iosfwd>`, `<streambuf>` and `<syncstream>` (the `reader` and `writer` concepts), and `<version>` (the compiler version is a metaprogram builtin if it is ever needed).

### 12. Every component is proved and tested

- A library module is accepted only when it proves with no unproved goals and no `--allow-unproved`. `assume`, `unsafe` and `@trusted` appear only in `Pia.Sys.Posix` and `Pia.Rt`, so `piac --trust-report` on any program that uses only the library lists nothing from it outside those two.
- Each module has a lit test in `tests/std/` that checks its goal counts, and a test program that runs it on examples, including the edge cases the C++ standard calls out (empty ranges, one element, all equal, the extreme values of each integer type).
- Proving the library is part of the build-time benchmark ([ADR 0032](0032-parallel-sliced-cached-proving.md)): `lib/` joins `tools/bench/baseline.json`, and a library PR that raises proof cost by more than the gate allows has to say why.

### 13. Phases

Each phase is a set of issues, one PR each, with a module, its tests, and its row of [docs/cpp-std.md](../cpp-std.md) updated.

1. **Phase 0.** This ADR, [docs/cpp-std.md](../cpp-std.md), and `lib/` with its Bazel rules and the `tests/std` harness.
2. **Phase 1, `Pia.Core` without allocation**, buildable today:
   1. the core bit builtins ADR 0023 lists and does not have yet (`clz`, `ctz`, `popcount`, `rotl`, `rotr`, `bswap`), then `Pia.Core.Bit` (`<bit>`);
   2. `Pia.Core.Int` (`gcd`, `lcm`, `midpoint`, `cmp_less` and friends, `in_range`, limits, saturating arithmetic);
   3. `Pia.Core.Order` (`Eq`, `Ord` with the strict weak order laws, `ordering`, `compare`, `swap`, `exchange`, lexicographic comparison);
   4. `Pia.Core.Option` and `Pia.Core.Result` (`<optional>`, `<expected>` without the monadic operations);
   5. `Pia.Core.Algo.Search`: `find`, `count`, `contains`, `equal`, `mismatch`, `starts_with`, `ends_with`, `search`, `adjacent_find`, `min_element`, `max_element`, `minmax_element`, `lexicographical_compare`, `is_sorted`, `is_sorted_until`;
   6. `Pia.Core.Algo.Modify`: `fill`, `copy`, `copy_backward`, `swap_ranges`, `reverse`, `rotate`, `shift_left`, `shift_right`, `replace`, `remove`, `unique`, and `<numeric>`'s `iota`, `accumulate`, `reduce`, `partial_sum`, `adjacent_difference`, `inner_product`, with overflow in their contracts;
   7. `Pia.Core.Algo.Sort` and `Heap` (binary search family, `make_heap` and friends, `sort` as heapsort first since it needs no recursion or buffer, `partial_sort`, `nth_element`, `partition`, `merge` into an `out` slice, `is_permutation`, `next_permutation`, `prev_permutation`), each sort proved to return a sorted permutation;
   8. `Pia.Core.Algo.Set` (`includes`, `set_union`, `set_intersection`, `set_difference`, `set_symmetric_difference` into `out` slices);
   9. `Pia.Core.Ascii`, `Pia.Core.Utf8` and integer `Pia.Core.Charconv`, with `to_chars`/`from_chars` round trips proved;
   10. `Pia.Core.Hash`, `Pia.Core.Rand` (integer engines such as `minstd_rand` and `mt19937`, and an unbiased `uniform_int`), `Pia.Core.Ratio` and `Pia.Time`'s durations and civil calendar.
3. **Phase 2, containers and strings over `Pia.Mem`**, with #72: `string`, `deque`, `flat_map`, `flat_set`, `priority_queue`, `stack`, `queue`, `unordered_map`, `unordered_set`, `map` and `set` (B-trees whose nodes live in a pool), `list` and `forward_list` (pool-indexed nodes), the box for `unique_ptr`, and the algorithms that need a buffer (`stable_sort`, `stable_partition`, `inplace_merge`).
4. **Phase 3, the outside world**, after `Pia.Sys` and `Pia.Io` (#57, #58): `format`, `print`, readers and writers for the stream headers, `<filesystem>`, `<cstdio>`, `<chrono>`'s clocks, `<stacktrace>`.
5. **Phase 4, floats** (M11): `Pia.Math`, floating-point `<charconv>`, the floating-point distributions.
6. **Phase 5, concurrency** (M12): `Pia.Sync`, `Pia.Task`, `Pia.Chan`, as ADR 0027 designs them.
7. **Phase 6, function values**: the `_if` algorithms, `transform`, comparator overloads, monadic `option` and `result`, `<functional>`, and `<ranges>`'s views.
8. **Later**: `<regex>`, `<mdspan>` (with value parameters in generic types), time zones, Unicode tables, `shared_ptr`.

### 14. Language gaps are listed, not worked around

Where the library needs something the language does not have, the library waits for it, and the gap is an issue of its own. Known now:

| Gap | Blocks |
| --- | --- |
| Imported types and generic functions across interfaces ([ADR 0039](0039-module-and-interface-syntax.md) step 3) | every program importing a generic library module; until then a module's generics are proved by the definition check, and its tests are in the module's own test file |
| Function values and closures ("functions as values are not supported yet") | phase 6: predicates, operations, views, `<functional>` |
| Value parameters in generic types (`[t; n]` for a parameter `n`; designed in [design.md](../design.md)) | `std::array` algorithms generic over `N`, `bitset<N>`, `inplace_vector<T, N>`, `mdspan` extents |
| Core tuple types, values and patterns (section 9; an ADR of their own) | `<tuple>`, `pair` as a tuple, structured bindings, `apply`, argument packs for `format` and `make_unique`, multi-value returns in `<algorithm>` (`minmax`, `mismatch`) |
| Anonymous sum types | `std::variant<Ts...>` beyond named variants, and `visit` over one |
| Recursive types | proved `shared_ptr` cycle freedom, recursive values such as a JSON tree; the node containers use pool indices instead, which is their design rather than a workaround |
| Calls inside a callee's `ensures` are unconstrained at the caller | composing generic algorithms whose contracts name each other's spec functions |
| Floats (M11), atomics and the concurrency runtime (M12) | phases 4 and 5 |
| Cost proofs | proving C++'s complexity guarantees |
| Payloads of fixed-array type in constructors, partial moves, `@derive(drop)` | some container element types |

## Consequences

- A C++ programmer can find every `std` facility, or why it is missing, from one page, and the page stays current because every library PR updates it.
- Pia's library promises more than C++'s: each function's contract is its specification, proved, and C++'s undefined behaviour becomes a compile-time obligation on the caller.
- Some C++ idioms do not survive: iterator pairs, exceptions, default allocators, comparator objects in containers' types, locales and wide strings. Each has a stated replacement.
- The phases are ordered by what the language can do today, so most of `<algorithm>`, `<bit>`, `<numeric>`, `<charconv>` and `<compare>` can land before function values or floats, and the gap table says which language work unblocks the most of the rest.
- The library becomes the largest body of proved Pia code, so it is also the main test of the verifier's speed and of [ADR 0037](0037-idiomatic-pia-and-lints.md)'s idioms; slow or awkward proofs found here become verifier issues.
