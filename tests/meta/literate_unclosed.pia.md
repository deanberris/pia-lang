A code block with no closing fence is an error.

// RUN: not piac --check %s 2>&1 | FileCheck %s
CHECK: literate_unclosed.pia.md:6:1: error: this ```pia code block is never closed

```pia
let x : u8 = 1
