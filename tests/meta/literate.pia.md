# A literate Pia program

A `.pia.md` file is Markdown. Only the fenced `pia` blocks are code, and the
prose before each block documents its first item (ADR 0029).

// RUN: piac --verify %s | FileCheck %s
// RUN: piac --dump-ast --comments %s | FileCheck %s --check-prefix=AST

## Saturating increment

`bump` adds one and stops at 255 instead of wrapping.

```pia
let bump (x : u8) : u8
  ensures result >= x
  = x +| 1
```

Other fences are prose, so this is not compiled:

```ocaml
let broken = (
```

## Doubling

Doubling into a wider type cannot overflow.
```pia
let double (x : u8) : u16
  ensures result = 2 * x
  = x * 2  \ u16 holds 510
```

The end of the file is prose too.

<!--
CHECK: literate.pia.md:15:3: proved: the postcondition holds [smt]
CHECK: literate.pia.md:30:3: proved: the postcondition holds [smt]
CHECK: 2 proved, 0 failed, 0 skipped

AST:      (Program
AST-NEXT:   (Comment "The end of the file is prose too.{{.*}}" [prose detached])
AST-NEXT:   (LetItem "bump"
AST-NEXT:     (Comment "# A literate Pia program{{.*}}`bump` adds one and stops at 255 instead of wrapping." [prose leading])
AST:        (LetItem "double"
AST-NEXT:     (Comment "Other fences are prose{{.*}}Doubling into a wider type cannot overflow." [prose leading])
AST:            (Comment "u16 holds 510" [line trailing])
-->
