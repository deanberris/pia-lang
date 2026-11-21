# Errors in literate files

Each code block must close what it opens, and the last block must be
closed by a fence.

// RUN: not piac --check %s 2>&1 | FileCheck %s

CHECK: literate_errors.pia.md:11:21: error: the code block ends before '(' is closed

```pia
let pair : u8 = add (1
```

CHECK-NOT: error
