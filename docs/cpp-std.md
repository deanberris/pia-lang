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
| `<compare>` | `Pia.Core.Order`: `ordering` (`strong_ordering`: `Less`, `Equal`, `Greater`) and `compare`, generic over `Ord` and for each integer type; `partial_ordering` and `weak_ordering` wait for floats and for types with equivalent but distinct values; `@derive(ord)` waits for exported metaprograms | Direct | `ordering`, `compare` done (importing them waits for imported types) |
| `<utility>` | `swap`, `exchange` in `Pia.Core.Order`, of a slice's elements, since Pia has no references to scalars; `cmp_equal`, `cmp_less` and the other safe comparisons are Pia's own `=`, `<` and so on, which compare integers of any two types exactly (an `i32` below a `u32` is `a < b`), so `Pia.Core.Int` does not repeat them; `in_range` is a narrowing goal (`let y : u8 = x` proves `x` fits) until a type's bounds can be values in generic code; `pair` is a two-element tuple (core tuples, ADR 0040 section 9); `move`, `forward` are the `moved` modifier; `to_underlying` is `widen`; `unreachable` is a proof goal (`assert false`) | Direct and Core | safe comparisons done (core); `swap`, `exchange` done (an interface cannot state their postconditions yet) |
| `<optional>` | `Pia.Core.Option`: the generic `option t` (`None`, `Some`), `has_value`, `is_none`, `value_or`; the core has no `option`, so the module defines it | Direct; monadic `and_then`, `transform`, `or_else` deferred | done in the module, but nothing is importable until an interface can list a generic type (ADR 0039 step 3); `value` waits for `abort` at a type parameter, comparisons for importing `Pia.Core.Order`'s concepts; monadic operations phase 6 |
| `<expected>` | `Pia.Core.Result` over the core `result t e` and `?`: `has_value`, `value` and `error` (C++'s undefined behaviour and exceptions as preconditions), `value_or`, `error_or`, and `==` as `same`; exported for `result t u32` with `t` one of `u8`, `u32`, `u64`, `i32`, `i64` | Direct; monadic operations deferred | done for those instances (other `e` wait for importing the error's type, and generic `t` and `e` for importing generic functions); monadic operations phase 6 |
| `<variant>` | sum types and `match` | Core; `variant<Ts...>` and `visit` need anonymous sum types | n/a |
| `<tuple>` | core tuple types `(u8, str)`, values `(a, b)`, `t.0` and tuple patterns; `apply`, `tuple_cat`, `tuple_size`, `tuple_element` as metaprograms over tuple types; structural `Eq`, `Ord`, `Hash` | Core (ADR 0040 section 9) | deferred: core tuples need their own ADR |
| `<any>` | `dyn` | Out: no run-time type information (ADR 0003) | n/a |
| `<bitset>` | `Pia.Core.Bit` over `[u64; n]` | Direct | deferred: value parameters in generic types |
| `<functional>` | `Pia.Fn` | Deferred: function values | phase 6 |
| `<type_traits>` | type-level metaprograms and type `match`; `Pia.Core.Traits` as needed | Idiom (ADR 0035) | phase 1 as needed |
| `<typeinfo>`, `<typeindex>` | metaprogram builtins (`name`, `type_kind`) | Out: no RTTI | n/a |
| `<source_location>` | the core's source locations in diagnostics; a metaprogram builtin if a program needs one | Core | n/a |
| `<initializer_list>` | array literals | Core | n/a |
| `<version>` | none | Out | n/a |
| `<stacktrace>` | `Pia.Rt` | Direct (#58) | phase 3 |
| `<exception>`, `<stdexcept>` | closed error variants in `result` (ADR 0028) | Out: no exceptions | n/a |
| `<system_error>`, `<cerrno>` | each module's error variants; `Pia.Sys` decodes `errno` | Idiom | phase 3 |
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
| `<memory>` | `Pia.Mem`: allocators (ADR 0026); `unique_ptr` is a `@linear` or `Drop` box; `uninitialized_*` are `out` slices | Idiom | phase 2 |
| `shared_ptr`, `weak_ptr` | `Pia.Mem.Rc` | Deferred: atomics, recursive types | later |
| `<memory_resource>` | `arena` (`monotonic_buffer_resource`), `pool` (`unsynchronized_pool_resource`), `shared` (`synchronized_pool_resource`) | Direct: every Pia container is a `pmr` container | #59, #71 |
| `<new>` | allocation is a `Pia.Mem` call returning `result`; there is no `new`, no placement `new` (`out` memory is written instead) and no `bad_alloc` (`OutOfMemory`) | Idiom (ADR 0026) | n/a |
| `<scoped_allocator>` | nothing to do: allocators are passed explicitly | Out | n/a |

## Strings and text

| Header | Pia | Kind | Status |
| --- | --- | --- | --- |
| `<string_view>` | `str`, a `[u8]` slice refined to valid UTF-8, with `Pia.Core.Utf8` | Idiom | phase 1 |
| `<string>` | `Pia.Text.String` over `Pia.Mem.Vec` | Direct; every string takes an allocator | phase 2 |
| `<cstring>` | slice algorithms (`copy` for `memcpy`, `equal` and `lexicographical_compare` for `memcmp`, `find` for `memchr`); no NUL-terminated strings | Idiom | phase 1 |
| `<charconv>` | `Pia.Core.Charconv`: `to_chars`, `from_chars` for integers in bases 2 to 36, with round trips proved | Direct; floats deferred (M11) | phase 1, phase 4 |
| `<format>`, `<print>` | `Pia.Text.Format`: format strings checked at compile time by a metaprogram; `Format` concept instead of `formatter` | Direct | phase 3 |
| `<cctype>` | `Pia.Core.Ascii` | Direct, ASCII only | phase 1 |
| `<cuchar>` | `Pia.Core.Utf8` (encode, decode, validate) | Direct | phase 1 |
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
| `<vector>` | `Pia.Mem.Vec` | Direct (#86) | in progress (#86) |
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
| `<algorithm>` modifying | `Pia.Core.Algo.Modify` | Direct | phase 1 |
| `<algorithm>` sorting, binary search, heap | `Pia.Core.Algo.Sort`, `Pia.Core.Algo.Heap`; stable forms need an allocator | Direct | phase 1, phase 2 |
| `<algorithm>` set operations | `Pia.Core.Algo.Set`, into `out` slices | Direct | phase 1 |
| `<algorithm>` permutations | `Pia.Core.Algo.Perm` | Direct | phase 1 |
| `<algorithm>` `_if` forms, `transform`, comparator overloads | the same functions with a function parameter | Deferred: function values | phase 6 |
| `<numeric>` | `Pia.Core.Int` (`gcd`, `lcm`, `midpoint`), `Pia.Core.Algo.Modify` (`iota`, `accumulate`, `reduce`, `partial_sum`, `adjacent_difference`, `inner_product`) | Direct | `gcd` (of signed values, unsigned), `midpoint` done; `gcd`'s contract does not yet say it divides both, and `lcm` waits, both for nonlinear facts the verifier cannot prove yet; the algorithms phase 1 |
| C++26 saturation (`add_sat`, `sub_sat`, `mul_sat`, `div_sat`, `saturate_cast`) | `add_sat`, `sub_sat` are the core builtins (`+|`, `-|`); `mul_sat`, `div_sat` and `saturate_cast_<t>` (from `i64` and `u64`, since the target cannot be a type argument yet) in `Pia.Core.Int` | Direct | done |
| `<execution>` | `spread` and `Pia.Par` | Idiom (ADR 0014) | deferred: M12 |
| `<generator>` | coroutines | Deferred (ADR 0027) | phase 5 |

## Numerics and time

| Header | Pia | Kind | Status |
| --- | --- | --- | --- |
| `<bit>` | core builtins `popcount`, `clz` (`countl_zero`), `ctz` (`countr_zero`), `rotl`, `rotr` (amount proved below the width) and `bswap` (`byteswap`); the rest (`bit_width`, `bit_floor`, `bit_ceil`, `has_single_bit`, `countl_one`, `countr_one`, `endian`) in `Pia.Core.Bit` | Direct | builtins done; `Pia.Core.Bit` done, except `bit_cast` (needs a byte view of any type) |
| `<cmath>`, `<numbers>`, `<complex>`, `<cfenv>` | `Pia.Math`, proved in Pia, never libm | Direct | deferred: floats (M11) |
| `<valarray>` | `vec<T, k>` and `spread` | Out | n/a |
| `<random>` | `Pia.Core.Rand`: integer engines and integer distributions; floating-point distributions later | Direct | phase 1, phase 4 |
| `<ratio>` | `Pia.Core.Ratio`: rationals folded at compile time | Direct | phase 1 |
| `<chrono>`, `<ctime>` | `Pia.Time`: integer durations, time points and the civil calendar; clocks over `Pia.Sys.Clock`; time zones later | Direct | phase 1, phase 3, later |

## Input and output

| Header | Pia | Kind | Status |
| --- | --- | --- | --- |
| `<iostream>`, `<istream>`, `<ostream>`, `<ios>`, `<iomanip>` | `Pia.Io`'s `reader` and `writer` concepts, and `Pia.Text.Format` | Idiom | phase 3 |
| `<fstream>` | `Pia.Io` over `Pia.Sys.Fs` | Direct | phase 3 |
| `<sstream>`, `<spanstream>` | writers into a `Pia.Text.String` or an `out` slice | Direct | phase 3 |
| `<iosfwd>`, `<streambuf>`, `<syncstream>` | none | Out: no stream class hierarchy | n/a |
| `<cstdio>` | `Pia.Io` | Idiom | phase 3 |
| `<filesystem>` | `Pia.Sys.Fs` | Direct (#57) | phase 3 |

## Concurrency

All of these are designed in [ADR 0027](adr/0027-coroutines-and-race-freedom.md) and wait for M12.

| Header | Pia | Kind | Status |
| --- | --- | --- | --- |
| `<atomic>` | core atomic builtins on `atomic<T>` | Core | phase 5 |
| `<thread>`, `<stop_token>` | `Pia.Task`: structured scopes and cancellation tokens | Idiom | phase 5 |
| `<mutex>`, `<shared_mutex>`, `<condition_variable>`, `<semaphore>`, `<latch>`, `<barrier>` | `Pia.Sync`: locks that own their data, with lock levels | Idiom | phase 5 |
| `<future>` | `Pia.Task`'s `join`, and `Pia.Chan` | Idiom | phase 5 |
