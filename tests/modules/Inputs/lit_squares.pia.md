# Squares, a literate module

A literate module exports its specification functions with their
definitions, as a plain one does.

```pia
module Num.Squares : Squares

interface Squares = sig
  let spec sq : (x : u8) -> u16
  let spec small : (x : u8) -> bool
end
```

Prose between the blocks is not part of a definition.

```pia
let spec sq (x : u8) : u16 = x * x
```

```pia
let spec small (x : u8) : bool @opaque = sq x < 100
```
