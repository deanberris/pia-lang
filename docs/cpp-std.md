# The C++23 standard library in Pia

Status: proposed design ([ADR 0040](adr/0040-cpp23-standard-library-in-pia.md)). This page maps every C++23 standard header onto the Pia module that provides it, and is updated by each library pull request, so it is also the library's status page. The first pieces are in the core, and `lib/` has its first modules, `Pia.Core.Bit`, `Pia.Core.Int`, `Pia.Core.Order`, `Pia.Core.Option` and `Pia.Core.Result` (`lib/Pia/Core/`, tested in `tests/std/`).

Pia gives what the C++ library lets a program do, in Pia's idioms: slices instead of iterator pairs, `result` and `?` instead of exceptions, explicit allocators instead of `std::allocator`, concepts instead of comparator objects, and metaprograms instead of type traits. Every function has a contract that the compiler proves, so what is undefined behaviour in C++ is a proof goal at the call in Pia.

**Kinds.** *Direct*: the same capability under a Pia name. *Idiom*: replaced by a different Pia mechanism, named in the row. *Core*: already part of the language. *Deferred*: waits on the named language or library work. *Out*: not provided, for the reason given.

**Status.** *planned* (phase number from the ADR), *done* (with the pull request), or *n/a*.

## Language support and utilities

| Header | Pia | Kind | Status |
| --- | --- | --- | --- |
| `<concepts>` | `Pia.Core.Order`'s `Eq` (`same`: reflexive, symmetric, transitive) and `Ord` (`less`: a strict weak order, asymmetric by contract), with instances for every integer type and `bool`; `Pia.Core.Int` (`Integral`); the rest are concepts written where needed | Idiom: concepts with laws (ADR 0034) | `Eq`, `Ord` done, used inside `Pia.Core.Order`; importing a concept waits for ADR 0039 step 3 |
| `<coroutine>` | the core's `wait`, `yield` and `@suspends` | Core (ADR 0027) | deferred: M12 |
| `<compare>` | `Pia.Core.Order`: `ordering` (`strong_ordering`: `Less`, `Equal`, `Greater`) and `compare`, generic over `Ord` and for each integer type; `partial_ordering` and `weak_ordering` wait for floats and for types with equivalent but distinct values; `@derive(ord)` waits for exported metaprograms | Direct | `ordering`, `compare` done, exported with the generic `compare`, `min`, `max`, `clamp`, `swap`, `exchange`, `lex_compare`, `lex_compare_three_way` and the spec function `lex_from` (ADR 0039 step 3); `lexicographical_compare` is stated exactly as `lex_from` |
| `<utility>` | `swap`, `exchange` in `Pia.Core.Order`, of a slice's elements, since Pia has no references to scalars; `cmp_equal`, `cmp_less` and the other safe comparisons are Pia's own `=`, `<` and so on, which compare integers of any two types exactly (an `i32` below a `u32` is `a < b`), so `Pia.Core.Int` does not repeat them; `in_range` is a narrowing goal (`let y : u8 = x` proves `x` fits) until a type's bounds can be values in generic code; `pair` is a two-element tuple (core tuples, ADR 0040 section 9); `move`, `forward` are the `moved` modifier; `to_underlying` is `widen`; `unreachable` is a proof goal (`assert false`) | Direct and Core | safe comparisons done (core); `swap`, `exchange` done (an interface cannot state their postconditions yet) |
| `<optional>` | `Pia.Core.Option`: the generic `option t` (`None`, `Some`), `has_value`, `is_none`, `value_or`, and `==` and `<` as `same` and `less` over `Eq` and `Ord` (nullopt first); the core has no `option`, so the module defines it | Direct; monadic `and_then`, `transform`, `or_else` deferred | done, and exported as a generic type and functions (interface `Optional`), proved at each instance (ADR 0043); `value` waits for `abort` at a type parameter; monadic operations phase 6 |
| `<expected>` | `Pia.Core.Result` over the core `result t e` and `?`: `has_value`, `value` and `error` (C++'s undefined behaviour and exceptions as preconditions), `value_or`, `error_or`, and `==` as `same`; exported for `result t u32` with `t` one of `u8`, `u32`, `u64`, `i32`, `i64` | Direct; monadic operations deferred | done; `has_value`, `value_or`, `error_or` and `same` (over `Eq`) are also exported generic over `t` and `e`, so a module uses them with its own error types; `value` and `error` stay per instance until `abort` works at a type parameter; monadic operations phase 6 |
| `<variant>` | sum types and `match` | Core; `variant<Ts...>` and `visit` need anonymous sum types | n/a |
| `<tuple>` | core tuple types `(u8, str)`, values `(a, b)`, `t.0` and tuple patterns; `apply`, `tuple_cat`, `tuple_size`, `tuple_element` as metaprograms over tuple types; structural `Eq`, `Ord`, `Hash` | Core (ADR 0040 section 9) | deferred: core tuples need their own ADR |
| `<any>` | `dyn` | Out: no run-time type information (ADR 0003) | n/a |
| `<bitset>` | `Pia.Core.Bit` over `[u64; n]` | Direct | deferred: value parameters in generic types |
| `<functional>` | `Pia.Fn`: the laws of function arguments (`strict_weak_order`, `equivalence`, `associative`, `commutative`, `identity`, `sorted`, ...), generic spec functions exported with their definitions (ADR 0044, step 5) | Laws done; the rest of <functional> waits for the library | phase 6 |
| `std::hash` (`<functional>`) | `Pia.Core.Hash`: the `Hash` concept over `Eq`, whose law `agrees` says `same a b ==> hash a = hash b`; `hash` for the eight integer types, `bytes` (FNV-1a, 64 bits), `combine` and `hash_all` over any Hash type | Direct; the function is fixed, so a hash is the same on every target and every run, where C++ leaves it unspecified | done: integers hash their 64-bit two's complement encoding with SplitMix64's finaliser, and each instance's law is proved where a generic function uses it, as for `Eq` and `Ord` (81 goals); tuples and records wait for structural instances (ADR 0040 section 9) |
| `<type_traits>` | type-level metaprograms and type `match`; `Pia.Core.Traits` as needed | Idiom (ADR 0035) | phase 1 as needed |
| `<typeinfo>`, `<typeindex>` | metaprogram builtins (`name`, `type_kind`) | Out: no RTTI | n/a |
| `<source_location>` | the core's source locations in diagnostics; a metaprogram builtin if a program needs one | Core | n/a |
| `<initializer_list>` | array literals | Core | n/a |
| `<version>` | none | Out | n/a |
| `<stacktrace>` | `Pia.Rt` | Direct (#58) | phase 3 |
| `<exception>`, `<stdexcept>` | closed error variants in `result` (ADR 0028); an exception of any dynamic type is one case carrying a box over a concept, `Cxx of box exception` (ADR 0046, 2026-11-27 note) | Out: no exceptions; `std::exception_ptr` becomes a boxed error payload | a boxed error payload within a module done (tests/verify/box_error_payload.pia); across modules with ADR 0071's tables; the `exception` concept and catching at bound C++ calls with the C++ FFI (0.5) |
| `<system_error>`, `<cerrno>` | each module's error variants; `Pia.Sys` decodes `errno` | Idiom | `Pia.Sys.Fs.errno` done: `Pia.Sys.Posix.errno` reads the thread's errno through `@deref`, and Fs decodes it into a variant; the other `Pia.Sys` modules phase 3 |
| `<cassert>` | `assert` (proved, never checked at run time) | Core | n/a |
| `<limits>`, `<climits>`, `<cstdint>`, `<cstddef>`, `<cinttypes>` | the integer and range types, which state their bounds: `u8` is `int{0..255}`, and a range type is its own `numeric_limits`. Functions returning them per type wait for a type's bounds to be values in generic code | Core | core types done; generic limits wait |
| `<cfloat>`, `<stdfloat>` | `Pia.Math` | Deferred: floats (M11) | phase 4 |
| `<cstdlib>` | `abs` (its result is unsigned, so `abs` of the minimum is defined) and `div` (as `quot_rem`, since `div` is the core builtin, with a `quot_rem_i32` record per type) in `Pia.Core.Int`; `exit`, `getenv` in `Pia.Sys`; `malloc` is `Pia.Mem`; `qsort`, `bsearch` are `Pia.Core.Algo` | Direct | `abs`, `div` done; the rest phase 1, phase 3 |
| `<csignal>` | `Pia.Rt` | Direct (#58) | phase 3 |
| `<csetjmp>` | none | Out | n/a |
| `<cstdarg>` | none | Out: no C variadics | n/a |

## Memory

| Header | Pia | Kind | Status |
| --- | --- | --- | --- |
| `<memory>` | `Pia.Mem`: allocators (ADR 0026); no `unique_ptr`: one non-null `box t` or `box c` over a concept `c` (type-erased, contents proved to meet `c`; ADR 0040 section 4), freed through its stored allocator, `option (box t)` when it may be empty; `uninitialized_*` are `out` slices | Idiom | `box t` (ADR 0046 step 1) and `box c` for the verifier (steps 2 to 4: `widen` with the use check, calls through a box proved from the concept's contracts and one-value laws, `box c` meeting `c` by forwarding) done; code generation for `box c` within a module (a tagged union of the widened types, a switch on the tag, direct calls where it is known; step 5) done; function-pointer tables across modules (step 6), `remove`/`fill` on it phase 2; `Pia.Mem.Alloc` (`oom`, the `Allocator` concept, a bump allocator) and `Pia.Mem.Box` (`box t r` over any allocator, with `remove`, `free` and a `drop` at scope end) done; pools and pages phase 2 |
| `shared_ptr`, `weak_ptr` | `Pia.Mem.Ref`: `ref`, `weak` ([ADR 0047](adr/0047-recursive-sum-types-and-shared-references.md)) | Deferred: recursive types (ADR 0047); atomic `shared_ref` with M12 | later |
| `<memory_resource>` | `arena` (`monotonic_buffer_resource`), `pool` (`unsynchronized_pool_resource`), `shared` (`synchronized_pool_resource`) | Direct: every Pia container is a `pmr` container | #59, #71 |
| `<new>` | allocation is a `Pia.Mem` call returning `result`; there is no `new`, no placement `new` (`out` memory is written instead) and no `bad_alloc` (`OutOfMemory`) | Idiom (ADR 0026) | n/a |
| `<scoped_allocator>` | nothing to do: allocators are passed explicitly | Out | n/a |

## Strings and text

| Header | Pia | Kind | Status |
| --- | --- | --- | --- |
| `<string_view>` | `str`, a `[u8]` slice refined to valid UTF-8, with `Pia.Core.Utf8` | Idiom | phase 1 |
| `<string>` | `Pia.Text.String` over `Pia.Mem.Vec` | Direct; every string takes an allocator | phase 2 |
| `<cstring>` | slice algorithms (`copy` for `memcpy`, `equal` and `lexicographical_compare` for `memcmp`, `find` for `memchr`); no NUL-terminated strings | Idiom | phase 1 |
| `<charconv>` | `Pia.Core.Charconv`: `to_chars`, `from_chars` for integers in bases 2 to 36, with round trips proved | Direct; floats deferred (M11) | `from_chars` done for `u8`, `u16`, `u32`, `i8`, `i16` and `i32` in any base 2 to 36: the value exact as the spec `num`, saturated at one past the largest; on an error `value` is kept, `Invalid` when there are no digits and `OutOfRange` when they do not fit, as C++'s; one proof, `parse_digits`, scans for every type, and a signed type's contract is the one spec `signed_parse`. `to_chars` done for all eight integer types, lower-case, with a `-` for a negative value: ok exactly when the digits fit (`ndig`, how many v has), each byte a digit of the base, nothing written otherwise (C++'s `value_too_large`), and their value (`digits_value`, left-fold accumulator with opaque `digit_step` and `dig_count`) proved equal to `v` (or `0 - v` after `-`) so that `from_chars` reads `v` back via the exported lemmas `digits_frame`, `digits_value_eq_num` and `run_digits` (#306). Both 657 goals. `Pia.Core.Digits` (83 goals) also provides `dval`, `pow`, `divmod32`/`divmod64`, `prepend`, `frame`, `shift`, `step`, and `put`. Waiting: `from_chars` for `u64` and `i64`, whose overflow check divides by the base; phase 4 for floats |
| `<format>`, `<print>` | `Pia.Text.Format`: format strings checked at compile time by a metaprogram; `Format` concept instead of `formatter` | Direct | phase 3 |
| `<cctype>` | `Pia.Core.Ascii`: `is_digit`, `is_upper`, `is_lower`, `is_alpha`, `is_alnum`, `is_xdigit`, `is_space`, `is_blank`, `is_cntrl`, `is_print`, `is_graph`, `is_punct`, `to_upper`, `to_lower`, and `digit_value`/`digit`, `hex_value`/`hex_digit` | Direct, ASCII only | done: each classifier says exactly which bytes it holds for, as C++'s do in the "C" locale, bytes above 127 are in no class, and each digit pair is a round trip (66 goals); no locales |
| `<cuchar>` | `Pia.Core.Utf8`: `sequence_length`, `decode`, `encode`, `valid` | Direct | done, by the Unicode standard's table 3-7 (no overlong forms, no surrogates, nothing above U+10FFFF), with both round trips proved: decoding what `encode` wrote gives the scalar back, and a valid sequence's bytes are what `encode` writes for the value `decode` reads (`bytes_of`) (294 goals); `Pia.Text.Json.Spec`'s own `utf8_len` can move here next |
| `<cwctype>`, `<cwchar>` | none | Out: UTF-8 only | n/a |
| `<locale>`, `<clocale>`, `<codecvt>` | none | Out: no locales | n/a |
| `<regex>` | `Pia.Text.Regex`, a linear-time automaton engine | Deferred | later |

## Containers

All containers are in `Pia.Mem` (#72) and take an allocator. Element access is `c.[i]` with the bound proved; lookups by key return `option`.

| Header | Pia | Kind | Status |
| --- | --- | --- | --- |
| `<array>` | `[T; N]` and slice algorithms | Core | n/a |
| `<span>` | `[T]` slices and `xs.[a .. b]` | Core | n/a |
| `<mdspan>` | strided views over slices | Deferred: value parameters in generic types | later |
| `<vector>` | `Pia.Mem.Vec`: `vec t a r` holds its allocator `a` (any `Pia.Mem.Alloc.Allocator`) and a buffer from the region `r`; `with_capacity`, `push` (fallible, doubling plus one), `get`, `set`, `pop` | Direct (#86) | `vec t a r` done (lib/Pia/Mem/Vec.pia); `vec (box t)` proved as a prototype (tests/verify/vec_boxes.pia), moving in with box drop; insert, erase, iterators phase 2 |
| `<deque>` | `Pia.Mem.Deque`, a ring of blocks | Direct | phase 2 |
| `<list>`, `<forward_list>` | `Pia.Mem.List`, nodes in a pool linked by index | Direct | phase 2 |
| `<map>`, `<set>` | `Pia.Mem.Map`, `Pia.Mem.Set`: B-trees with nodes in a pool; the order is the key's `Ord` | Direct | phase 2 |
| `<unordered_map>`, `<unordered_set>` | `Pia.Mem.HashMap`, `Pia.Mem.HashSet`: open addressing over `Hash` and `Eq` | Direct | phase 2 |
| `<flat_map>`, `<flat_set>` | sorted `Vec`s with the binary search family | Direct | phase 2 |
| `<stack>`, `<queue>` | functions over `Vec` and `Deque`; `priority_queue` is `Pia.Mem.Heap` over the heap algorithms | Direct | phase 2 |
| C++26 `inplace_vector`, rings | `Pia.Core.Fixed` | Direct | deferred: value parameters in generic types |

## Iterators, ranges and algorithms

| Header | Pia | Kind | Status |
| --- | --- | --- | --- |
| `<iterator>` | slices, `usize` indices (with `len xs` for "not found"), and container cursors | Idiom | n/a |
| `<ranges>` | eager algorithms over slices; views such as `filter`, `transform`, `zip` | Deferred: function values | phase 6 |
| `<algorithm>` non-modifying | `Pia.Core.Algo.Search`: `find`, `count`, `contains`, `mismatch`, `equal`, `starts_with`, `ends_with`, `search`, `adjacent_find`, `min_element`, `max_element`, `minmax_element` (first smallest, last largest), `is_sorted_until`, `is_sorted`, exported as generic functions over `Pia.Core.Order`'s `Eq` and `Ord` and proved once (ADR 0043); a position is a `usize`, `len xs` when there is none. `Pia.Core.Order` has `min`, `max`, `clamp` (C++'s ties: the first argument when equivalent), `lexicographical_compare` (generic over `Ord`, proved once, exported for every integer type) and `lexicographical_compare_three_way` (for `u8`). Overloads taking a predicate or comparator wait for function values (section 6) | Direct | `Pia.Core.Algo.Search`, `Pia.Core.Order`'s done |
| `<algorithm>` modifying | `Pia.Core.Algo.Modify`: `fill`, `copy` and `copy_backward` into an `out` slice of the source's length, `swap_ranges`, `reverse`, `replace` (by value over `Eq`, or by a predicate as C++'s `replace_if`), `shift_left`, `shift_right` (the new end or start, as C++20), `remove` (in `Pia.Core.Algo.Remove`, so its proof runs in parallel: each kept element at its rank among them, a spec over `old xs`), each generic and proved once (ADR 0043) with every element of the result in its contract; `Pia.Core.Algo.Permutation`'s `occurrences` and `permutation` specs, for sorts | Direct | those done; `rotate` (three reversals proved at 280M) and `unique` (120M) wait for cheaper proofs, and `remove` and `unique` with a predicate with them |
| `<algorithm>` sorting, binary search, heap | `Pia.Core.Algo.Sort`, `Pia.Core.Algo.Heap`; stable forms need an allocator | Direct | `insertion_sort` and `exchange` (C++'s `iter_swap`) done, with a comparator that must be `Pia.Fn.strict_weak_order`, proved once, ensuring `Pia.Fn.sorted less xs` and `Pia.Core.Algo.Permutation.permutation xs (old xs)`; `Pia.Core.Algo.Heap`'s `is_heap_until`, `is_heap`, `push_heap`, `pop_heap`, `make_heap`, `sort_heap` and `sort xs less` (a heap sort), with the same comparator law, proved once (185 goals): the heap is stated parent to child, `(k - 1) >> 1`, `sort` ensures `Pia.Fn.sorted less xs` and `permutation xs (old xs)`; `sort xs` by `Ord`'s `less` waits for its proof from the comparator form; `Pia.Core.Algo.BinarySearch`'s `lower_bound`, `upper_bound`, `equal_range` and `binary_search`, by a comparator and by `Ord`, proved once (99 goals), with C++'s precondition: the range partitioned with respect to the value (`below`, `above`), which a sorted range meets; `equal_range` returns a `span` and is proved at its instances; `Pia.Core.Algo.Partition`'s `is_partitioned`, `partition_point` (by binary search) and `partition` (a permutation of the input), each with a predicate and proved once (57 goals); `Pia.Core.Algo.PartialSort`'s `partial_sort` (the first m sorted, none after them less, a permutation) and `nth_element` (as `partial_sort` of the first n + 1, O(n log n), with the stronger contract), proved once (82 goals); `Pia.Core.Algo.Merge`'s `merge` of two sorted ranges into an `out` slice (sorted, each value as often as in both, stable), proved once (57 goals); `next_permutation` and `prev_permutation` parked: their scans are cheap since #282 (a helper spec `rise` brought one from 232M to 3.5M), but reversing the suffix costs 482M on one invariant and the generic proof does not yet hold; stable forms phase 2 |
| `<algorithm>` set operations | `Pia.Core.Algo.Set` (`includes`, `set_intersection`, `set_difference`) `Pia.Core.Algo.SetUnion` (`set_union`) and `Pia.Core.Algo.SetSymmetric` (`set_symmetric_difference`), by a strict weak order, into the first `result` places of a destination at least as long as the output can be | Direct | done, proved once (75, 65 and 66 goals), on sets: ranges strictly increasing by `less`, where C++'s multiset semantics and membership (`member`, some element equivalent) agree; `includes` uses `binary_search`, O(m log n); each operation counts what it writes (`members`) and writes it strictly increasing; `set_union` (129M) and `set_symmetric_difference` (137M) cost most of the set operations to prove, so each is its own module and they prove in parallel; each operation's count is a spec of its own (`members`, `nonmembers`), which keeps the proofs cheap; multisets with duplicate elements wait |
| `<algorithm>` permutations | `Pia.Core.Algo.Perm` | Direct | phase 1 |
| `<algorithm>` `_if` forms, `all_of`/`any_of`/`none_of`, `transform`, comparator and operation forms | no `_if` names: overloads of `find`, `count`, `remove`, `replace`, `copy`, `sort`, `accumulate` and the rest that take a predicate, comparator or operation (`find xs p`, `sort xs less`); `all`, `any`, `none` | Idiom: overloads (ADR 0040 section 6) | `Pia.Core.Algo.Search`'s `find`, `count`, `all`, `any`, `none` with a predicate (proved once, over a `Function` object) and `mismatch`, `equal` with a binary predicate (proved at each call) done; `adjacent_find` with a predicate and the comparator forms of `min_element`, `max_element`, `minmax_element`, `is_sorted_until`, `is_sorted`, which require `Pia.Fn.strict_weak_order less` and are proved once (`is_sorted` says `Pia.Fn.sorted less xs`), done; the rest phase 6 |
| `<numeric>` | `Pia.Core.Int` (`gcd`, `midpoint`), `Pia.Core.Algo.Numeric` (`iota`, `accumulate`, `reduce`, `inner_product`, `transform_reduce`, `partial_sum`, `inclusive_scan`, `exclusive_scan`, `adjacent_difference`) | Direct | `gcd` (of signed values, unsigned), `midpoint` done; `gcd`'s contract states its exact value, the exported spec function `euclid`, and `divides` is exported with `quot_rem`; that `gcd` divides both, and `lcm`, wait for nonlinear facts the verifier cannot prove yet. `Pia.Core.Algo.Numeric`'s algorithms done, each with its operation as a function value and proved once (165 goals): the contract states the result as a left fold (`fold`, `fold2`, `scan1`, `iterate`), so overflow is the operation's, one written `@overflow(wrap)`, saturating, or with a `requires`; `reduce` and `transform_reduce` fold in order. `iota` counting by one also for each integer type but `i64`, requiring that the last value fits. Exact integer sums by `+` (an `int` spec against a fixed-width accumulator) and `iota` at `i64` wait for cheaper proofs |
| C++26 saturation (`add_sat`, `sub_sat`, `mul_sat`, `div_sat`, `saturate_cast`) | `add_sat`, `sub_sat` are the core builtins (`+|`, `-|`); `mul_sat`, `div_sat` and `saturate_cast_<t>` (from `i64` and `u64`, since the target cannot be a type argument yet) in `Pia.Core.Int` | Direct | done |
| `<execution>` | `spread` and `Pia.Par` | Idiom (ADR 0014) | deferred: M12 |
| `<generator>` | coroutines | Deferred (ADR 0027) | phase 5 |

## Numerics and time

| Header | Pia | Kind | Status |
| --- | --- | --- | --- |
| `<bit>` | core builtins `popcount`, `clz` (`countl_zero`), `ctz` (`countr_zero`), `rotl`, `rotr` (amount proved below the width) and `bswap` (`byteswap`); the rest (`bit_width`, `bit_floor`, `bit_ceil`, `has_single_bit`, `countl_one`, `countr_one`, `endian`) in `Pia.Core.Bit` | Direct | builtins done; `Pia.Core.Bit` done, with `native` shown as `Little` in the interface, except `bit_cast` (needs a byte view of any type) |
| `<cmath>`, `<numbers>`, `<complex>`, `<cfenv>` | `Pia.Math`, proved in Pia, never libm | Direct | deferred: floats (M11) |
| `<valarray>` | `vec<T, k>` and `spread` | Out | n/a |
| `<random>` | `Pia.Core.Rand`: integer engines and integer distributions; floating-point distributions later | Direct | phase 1, phase 4 |
| `<ratio>` | `Pia.Core.Ratio`: `reduce`, `add`, `subtract`, `multiply`, `divide`, `equal`, `less`, `less_equal` and the SI prefixes (`si "milli"`), metaprograms that fold ratios at compile time; `define` makes one a function whose contract gives its exact parts, and `check` is `static_assert` | Direct: C++ folds in its types, Pia in exported metaprograms (ADR 0039) | done: exact 128-bit arithmetic, always in lowest terms with a positive denominator; a zero denominator, division by zero or a part outside i64 is a compile-time error, as in C++; no proof obligations beyond `value`'s (1 goal) |
| `<chrono>`, `<ctime>` | `Pia.Time`: `standard ()` makes C++'s `nanoseconds` to `weeks`, each with `plus`, `minus`, `times`, `less`, `same` and a `to_<unit>` cast from every other; `duration x p` and `cast` make more, with any `Pia.Core.Ratio` period; time points and the civil calendar; clocks over `Pia.Sys.Clock`; time zones later | Direct: a duration's period is a ratio folded at compile time, not a template argument | durations done: a widening cast is exact, with a precondition that the count fits i64, and a narrowing one truncates toward zero, as `duration_cast` does; a cast between periods that do not divide each other is an error for now; what the metaprograms make is proved in the importer (239 goals for the standard set in `time_edges.pia`); civil calendar done: `ymd` (year_month_day) for years -1000000 to 1000000, `is_leap`, `last_day`, `days_from_civil` (sys_days of a date, Howard Hinnant's algorithm, with its exact value as the contract) and `civil_from_days`, with both round trips proved: a day number gives a valid date that maps back to it, and the lemma `unique` says a valid date with a date's day number is that date (232 goals); time points done: `time_point x d` (time_point<Clock, d>) with `plus`, `minus` and order, `point_cast` (time_point_cast), and `sys_days ()`, which makes `sys_days` and `sys_seconds` with `to_sys_days` and `to_ymd` over the calendar; clocks phase 3, time zones later |

## Input and output

| Header | Pia | Kind | Status |
| --- | --- | --- | --- |
| `<iostream>`, `<istream>`, `<ostream>`, `<ios>`, `<iomanip>` | `Pia.Io`'s `reader` and `writer` concepts, and `Pia.Text.Format` | Idiom | phase 3 |
| `<fstream>` | `Pia.Io` over `Pia.Sys.Fs` | Direct | phase 3 |
| `<sstream>`, `<spanstream>` | writers into a `Pia.Text.String` or an `out` slice | Direct | phase 3 |
| `<iosfwd>`, `<streambuf>`, `<syncstream>` | none | Out: no stream class hierarchy | n/a |
| `<cstdio>` | `Pia.Io` | Idiom | phase 3 |
| `<filesystem>` | `Pia.Sys.Fs` | Direct (#57) | files done, for both targets: a `@linear` `file` with `open_read`, `create`, `read_some`, `write_all` and `close`, each failure an `Err` of a decoded errno (27 goals); directories, `fstat` and seeking phase 3 |

## Concurrency

All of these are designed in [ADR 0027](adr/0027-coroutines-and-race-freedom.md) and wait for M12.

| Header | Pia | Kind | Status |
| --- | --- | --- | --- |
| `<atomic>` | core atomic builtins on `atomic<T>` | Core | phase 5 |
| `<thread>`, `<stop_token>` | `Pia.Task`: structured scopes and cancellation tokens | Idiom | phase 5 |
| `<mutex>`, `<shared_mutex>`, `<condition_variable>`, `<semaphore>`, `<latch>`, `<barrier>` | `Pia.Sync`: locks that own their data, with lock levels | Idiom | phase 5 |
| `<future>` | `Pia.Task`'s `join`, and `Pia.Chan` | Idiom | phase 5 |

## Pia-only modules

These have no C++ standard header. They are listed here because they are library modules with the same three tests each in `tests/std`.

| Module | What | Status |
| --- | --- | --- |
| `Pia.Image.Bits` | LSB-first bit fields over a byte slice, as GIF's LZW and deflate read them: `read_bits` and `write_bits` for fields of up to 16 bits, proved against `bits_at`, the field as its bits, with the write's frame proved ([ADR 0054](adr/0054-proved-gif-and-inflate-codecs.md)) | done (173 goals) |
| `Pia.Image.Raster` | image dimensions (`dims`), the index of a sample and the rows of a rectangle, each proved to lie below `size w h c` (ADR 0054) | done (50 goals) |
| `Pia.Image.Gif.Spec`, `Pia.Image.Gif.Lzw` | GIF's LZW decoder, codes of 3 to 12 bits with the deferred clear, into a caller's buffer with a 12288-byte dictionary table the caller lends; total on every input, each code's string proved to be the spec's (`sym`), every index proved below 2^m, and checked against giflib on five streams (ADR 0054) | done |
| `Pia.Image.Gif.Decode` | the GIF container: `info` (screen, frame count, NETSCAPE2.0 loop count) proved to return `Ok` exactly when `Gif.Spec`'s block grammar accepts the input, and `decode_frame`, which composites frames 0 to k into a caller's RGBA buffer with local or global palettes padded to 256 colours, interlacing (its row order proved a permutation), transparency, disposal and clipping to the screen; checked against giflib on three files, every truncation and every one-byte corruption (ADR 0054) | done |
| `Pia.Image.Gif.LzwEncode`, `Pia.Image.Gif.Encode` | animated GIF encoding: `encode_animation` writes a global palette, the NETSCAPE2.0 loop count, and per frame a Graphic Control Extension and only the rectangle that changed, LZW-coded over a hash in a caller's table with a clear when the dictionary fills; every code proved below 2^width at width at most 12, the output proved to fit in `size_bound` bytes, and Ok proved to be a GIF by `Gif.Spec`'s grammar with the frames and screen asked for; checked with giflib and `Gif.Decode` on two animations (ADR 0054) | done; the round trip waits on ADR 0058 |
| `Pia.Image.Gif.Quantise` | RGB to a palette of at most 256 colours and an index raster: the input's own colours when there are few enough (each pixel then proved to map to its exact colour), else median cut over caller-lent boxes and a histogram; every index proved below the palette size; and `encode_rgb_animation`, one shared palette for every frame; no claim about visual quality; checked with giflib on a 6-colour animation (exact) and a gradient (ADR 0054) | done |
| `Pia.Compress.Huffman`, `Pia.Compress.Inflate.Spec`, `Pia.Compress.Inflate`, `Pia.Compress.Zlib` | deflate and zlib decoding into a caller's buffer: canonical Huffman tables whose completeness is the Kraft sum, stored, fixed and dynamic blocks with every distance proved at most the bytes written, lengths and distances proved to be RFC 1951's base plus extra bits, and Adler-32 proved equal to RFC 1950's definition; checked against zlib on 13 streams, every truncation and every one-byte corruption (ADR 0054) | done; whole-stream conformance waits on ADR 0058 |
