# 77. A definition that states no contract takes the contract of the interface that lists it

Date: 2026-11-27

Status: Accepted (Dean, 2026-11-27)

## Context

An interface lists each function a module exports with its type and contract (ADR 0039). The module meets it by proof: the interface's `requires` must imply the definition's, and the definition's `ensures` must imply the interface's. That rule lets an interface promise less than the body proves. But it also means that, for the usual case where the two are the same, the module writes every contract twice, in the same file:

```ocaml
module Counting : Counter

interface Counter = sig
  let count_to : (n : u32) -> u32
    requires n < 1000
    ensures result = n
end

let count_to (n : u32) : u32
  requires n < 1000      (* the same contract, again *)
  ensures result = n
= ...
```

Dean (2026-11-27): "we need a way for an implementation to not repeat the interface declaration's contracts in a module. It seems ugly to have to repeat the contracts in the same file."

Leaving the definition's contract out does not work today. A definition with no contract has `requires true` and promises nothing, and on today's `latest` piac:

- **The interface check passes only when the body unfolds.** The check is a lemma that calls the function, so it sees the body only if `definesValue` unfolds it: a pure function of scalars with no loop, buffer, `abort` or recursion (docs/verifier.md, "Pure functions of scalars"). A `count_to` with a `while` loop fails it (`counterexample: m = 992`), because a call to a loop is taken on its contract, and the contract is empty.
- **Callers in the module never see the interface's contract.** A call inside the module is taken on the definition's contract, so `let five (k : u32) : u32 ensures result = 5 = count_to 5` fails (`counterexample: k = 0`), even though importers would prove it from the interface.
- **The body is never proved under the interface's precondition.** A body that needs `n < 1000` to avoid an overflow cannot use it.

Prior art. Ada lets a body omit the aspects its specification states: the `Pre` and `Post` of a subprogram declared in a package spec apply to its body, and SPARK proves the body against them. Eiffel's redefinitions inherit their ancestors' contracts and may only weaken `require` (`require else`) or strengthen `ensure` (`ensure then`). Dafny refines a module's abstract methods by repeating only the body, with the specification taken from the refined module. C++ contracts (P2900) are stated on the first declaration and may be omitted on a redeclaration, which then has the same contract.

## Decision

### 1. A definition that states no contract takes its interface's

When a function that an interface of its file lists is defined with no `requires`, `ensures`, `costs` or `reads` clause, it takes that interface's clauses, as if they had been written on the definition:

```ocaml
module Counting : Counter

interface Counter = sig
  let count_to : (n : u32) -> u32
    requires n < 1000
    ensures result = n
end

let count_to (m : u32) : u32
=
  let i : mutable u32 = 0 in
  while i < m
    invariant i <= m
    decreases m - i
  do
    i <- i + 1
  done;
  i

let five (k : u32) : u32
  ensures result = 5
= count_to 5
```

Everything that reads a definition's contract then reads the interface's. The body is proved against it, a caller in the module takes the function on it (`five` proves), and the interface check is met trivially, since the two contracts are the same. Nothing changes for importers: they always used the interface's contract.

The interface names the parameters its own way. The copy is renamed to the definition's names (the interface's `n` is `count_to`'s `m` above), so the definition is free to name them as it likes. If one of the interface's quantifier binders has the name of one of the definition's parameters, the renaming would capture it, and the compiler asks for one of the two to be renamed. Hygiene (ADR 0022) already forbids that shadowing in written code.

### 2. All or nothing (Dean, 2026-11-27)

A definition that states any of those clauses states its whole contract, and inherits nothing. Its contract is checked against the interface's as it is today (ADR 0039), so it may still be stronger than what the interface promises, and `tests/verify/modules.pia` is unchanged in meaning.

The alternative, inheriting clause by clause (a definition with an `ensures` and no `requires` takes the interface's `requires`), saves a line in some files, but a reader can no longer tell a definition's contract from the definition alone: adding an `ensures` to a definition would silently change its precondition. With all or nothing, a definition's contract is either all on the definition or all on the interface.

A `decreases` measure is not part of the contract. It is about the body, not about what callers get, so a definition with only a measure still inherits.

### 3. What inherits

- **Ordinary functions and lemmas** listed with `:` in an interface the module claims, in the same file (a module claims only interfaces declared in its own file, ADR 0039).
- **Not spec functions, generics or metaprograms.** These are exported with their definitions, and the definition's contract is the one importers get (`sameSignature`), so the interface entry is a copy of the definition's and there is nothing to inherit.
- **Overloads.** An interface entry is matched to the definition of the same name and arity, and, when the name is defined more than once, to the overload whose parameter types are written the same.
- **Several interfaces.** When two interfaces the module claims list the function with the same contract, it takes that contract. When their contracts differ, there is no one contract to take, and the compiler asks for the definition to state one that meets both, which the existing check then proves.

### 4. Where goals point

The inherited clauses keep their source locations, so a goal they raise points at the interface's line: a body that breaks the inherited `ensures` fails at the `ensures` in the interface. That is where the contract is written, and where it must be fixed or the body changed.

### 5. Where it is done

`inheritInterfaceContracts` in `src/syntax/Interfaces.cpp` copies the clauses into the definitions, after metaprograms expand and before anything reads a contract. `irgen::generate` runs it, so `piac`, `pia repl`, `pia mcp` and `pia-lsp` all see the same program, and `piac` runs it before the Lean statements are made (ADR 0061), so an inherited lemma's statement is the interface's. Running it twice changes nothing, since a definition that has inherited a contract states one.

The interface artifact (`.piai`) is the interface as written, so it and the interface hash are unchanged.

### 6. Steps

1. The rule, `tests/verify/inherited_contracts.pia`, and the docs and skills that teach modules. Done (PR #500).
2. A lint, `repeated_contract`, for a definition whose contract is exactly its interface's, parameter names aside, with the fix of deleting it (`tests/lint/repeated_contract.pia`). Foreign functions keep theirs, since the bindings generator writes the contract on every row. The repository moved to the short form in the same change (Dean, 2026-11-27): 527 clauses on about 210 definitions in 67 files, the standard library, `tests/codegen`, `tests/modules`, the demos and the literate pages. Done.
3. `pia-lsp` hover shows an inherited contract on the definition, renamed to its parameters and marked with the interface it came from (`tests/lsp`). Done.

## Consequences

- **A contract is written once.** A module whose definitions match their interfaces writes each contract in one place, where importers read it. The interface stays the module's documentation.
- **Soundness is unchanged.** The definition is proved against exactly the contract it would have had if the clauses were written on it, so every existing argument (ADR 0039's check, `modular` in `tests/lean/CallRule.lean`) applies as it does to written contracts.
- **A changed meaning for an uncontracted definition.** A listed definition with no contract used to have `requires true` inside the module. Now it has the interface's precondition, so a caller in the module that called it outside that precondition gets a failed goal. Only two files in the repository define a listed function with no contract: `tests/verify/modules.pia`, whose `double` now states the weaker contract the test is about, and `tests/grammar/valid/module_header.pia`, which is only parsed.
- **Proof cost.** A definition that inherits a contract proves it, which costs what writing the contract costs. Its interface check becomes trivial.
- **Reading a definition.** A definition with no contract no longer means "promises nothing" if an interface lists it. The interface is in the same file, and step 3 shows the inherited contract on hover.
