# 59. Digits group with `'` or `_`; `min t` and `max t` are an integer type's bounds, folded to literals

Date: 2026-11-23

Status: Accepted (Dean, 2026-11-23). Dean asked for both parts, chose the spelling `min u8` / `max u8`, and asked that the bounds follow the target.

## Context

Dean noticed (2026-11-23) bare bound constants across the library: `4294967295`, `9223372036854775808`, `65535`. They are hard to read and easy to get wrong by one digit, and nothing ties `65535` to `u16`. `lib/Pia/Core/Int.pia` alone spells out every bound of u16 to u64 and i16 to i64, several times each, in its saturating contracts. He asked for two things:

1. digit separators in number literals, such as `100,000` or `100'000`;
2. named constants for type bounds, so that code stops using bare numbers. He prefers them as functions of the type, `min u8 = 0`, rather than a table of names, and wants them to follow the target.

Two facts constrain the design. Pia has no shadowing at all ([ADR 0022](0022-metaprogram-hygiene.md)), and `min` and `max` are already taken: `Pia.Core.Order` exports `min a b` and `max a b` at every width, and `Pia.Core.Charconv` has a local called `max`. And a `let` constant is an unknown value inside a contract (the pia-language skill's pitfalls), so `let u16_max : u32 = 65535` would not help the very contracts that need it most.

## Decision

### 1. Digits group with `'` or `_`

`100'000`, `0xFFFF'FFFF`, `0b1010'0101`, `4'294'967'295u64` and `1'000.25` are literals. A `'` must sit between two digits of the literal's base, as in C++14, so `100'` and `1'_0` are errors. `_`, which the lexer already accepted, keeps its looser rule, so no code changes. Separators mean nothing to the value: every reader of a literal's text (Sema, IRGen, the metaprogram interpreter, the lints) skips both, through one helper, `syntax::isDigitSeparator`.

`,` cannot group digits. It separates tuple elements and arguments, so `f (1,000)` would be ambiguous. Dean typed a typographic `’` (U+2019), which a phone substitutes for `'`; Pia's source is ASCII outside strings and comments, so only `'` is accepted.

`'` was free after a digit: inside a name it is a prime (`x'`), and a name never starts with a digit.

### 2. `min t` and `max t`

`min t` and `max t` are the least and greatest values of the integer type `t`: `min u8 = 0`, `max u16 = 65535`, `min i64 = -9223372036854775808`, `max byte` for `let byte = u8`, and the bounds of a range type named by a `let`.

- **They overload `min` and `max` by argument.** A call of `min` or `max` with one argument that names an integer type is a bound. Every other call, such as `Order.max a b`, resolves as before. Neither name is reserved, so `Pia.Core.Order` keeps its functions and Charconv's local `max` stays; where a local `max` is in scope, `max u8` is that local applied to `u8`, which is an error, as shadowing would have been.
- **They fold to literals.** IRGen replaces `max u16` with the literal `65535` before overload resolution, so it takes its context's type like any literal, and works in contracts, where a `let` constant would be unknown. `ensures a * b > max u16 ==> result = max u16` reads as the number did and proves the same way, with no cost.
- **They follow the target.** Each bound comes from the type as Sema resolves it, so `max usize` and `min isize` are the bounds of the target's `usize` ([ADR 0049](0049-targets-are-theories.md)). Both of Pia's models have 64-bit pointers today, and `piac` refuses a model with other pointers until `usize` follows the model's `ptr_bits`; when it does, `max usize` follows with it, and code that wrote `max usize` instead of `18446744073709551615` is already right.
- **Metaprograms.** Dean's `min u8 = 0` is the reading of a type-level function. In ordinary code the fold is done by IRGen, since an ordinary expression has no metaprogram calls. Inside a metaprogram, `range_of t` ([ADR 0056](0056-tests-generated-from-contracts-and-theories.md)) already gives `[lo; hi]`.

Not yet: `max t` for a generic body's type parameter `t`. A generic body is checked once, against a stand-in type ([ADR 0043](0043-generic-definitions-proved-once.md)), whose bounds are not known. This is the `numeric_limits` gap that `Pia.Core.Int` documents. It needs a concept that promises bounds, and is left for a later ADR.

### Alternatives

- **Named constants in a module**, `Limits.u32_max`: a name per type and bound, and a `let` constant is unknown in contracts unless it becomes a spec function. Rejected.
- **Members of the type**, `u32.max`: reads well, but `.` after a type name is new syntax, and types as values have no fields today.
- **Other names**, `lowest`/`highest` or `min_of`/`max_of`: no overloading, but Dean chose `min`/`max`.

## Consequences

- The library's bare bounds become `min t` and `max t`, starting with `Pia.Core.Int`, `Order`, `Bit` and `Image`.
- `docs/grammar.md` documents the separators, `docs/irgen.md` the bounds, and the pia-language skill both. The VS Code grammar and the reference lexer in `grammar/pia_lexer.py` accept `'`.
- Tests: `tests/grammar` (valid and invalid separators, shared by both lexers), `tests/verify/digit_separators.pia` and `tests/verify/type_bounds.pia`.
