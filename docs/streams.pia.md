# Demo: stream delineation

Rain that falls on a landscape runs downhill, gathers in valleys and becomes
streams. *Stream delineation* recovers those streams from a terrain model:
given the height of every point on a grid, it works out where the water on
each cell goes, how much water passes through each cell, which cells carry
enough to be a stream, and which outlet each cell drains to (its watershed).
It is Pia's flagship demo
([ADR 0016](adr/0016-stream-delineation-flagship-demo.md)), and its second
half moves sediment down those streams, with the total mass proved to stay
the same exactly ([sediment.pia.md](sediment.pia.md)).

This page is the program. It is a literate Pia file,
[`docs/streams.pia.md`](https://github.com/deanberris/pia-lang/blob/main/docs/streams.pia.md):
the prose is Markdown, the fenced `pia` blocks are the code, and `piac`
reads the whole file, attaching each paragraph to the function after it
([ADR 0029](adr/0029-comments-as-syntax-and-literate-pia.md)). The build
proves every goal in it before it generates any code, so what you read here
is what was proved and what runs.

To run it on a Mac with Apple Silicon:

```console
$ bazel run //examples/streams
$ bazel run //examples/streams -- ~/Pictures/terrain.png ~/Desktop/streams.png
```

The first command draws a synthetic terrain, saves it as
`streams-input.png` in the current directory, and writes the result to
`streams-output.png`. It prints a text preview of the map and how long
each stage took; on an M-series iMac the whole 384x256 map takes about 30
ms. The second reads your own heightmap, in any format
macOS can open (PNG, GIF, JPEG, TIFF, BMP), where brighter means higher, and
writes the map as PNG, or GIF if the name ends in `.gif`. Use a 16-bit heightmap
where you can: an 8-bit one has only 256 levels, so its terraces become
flats, and filling slopes each flat gently towards its outlet, which the
map shows as lake.

## The pipeline

```mermaid
flowchart LR
  dem["heights<br/>(dem)"] --> fill["1. fill sinks"]
  fill --> dirs["2. D8 directions"]
  dirs --> acc["3. accumulate,<br/>label watersheds"]
  acc --> render["4. streams and<br/>colours"]
  render --> png["PNG / GIF"]
  acc --> sed["5. sediment<br/>transport"]
  sed --> png2["PNG by load"]
```

1. **Fill sinks.** Real elevation data has pits, cells lower than all their
   neighbours, where water would get stuck. Filling raises each pit to the
   level where it spills, so every cell has a way down to the edge.
2. **D8 flow directions.** Each cell sends its water to the one neighbour,
   of its eight, down the steepest slope.
3. **Flow accumulation.** Following the directions from every cell counts
   how many cells drain through each cell, and the cell where each path
   ends labels its watershed.
4. **Streams.** A cell is part of a stream when at least `threshold` cells
   drain through it. The last stage colours the map: streams in blue,
   filled pits as lakes, and every other cell by its watershed, shaded by
   height.
5. **Sediment.** Water carries sediment down the same paths, eroding where
   it can carry more and depositing where it carries too much, and the
   stream cells are coloured by the load they carry.

What the verifier proves, function by function, is summed up
[at the end](#what-is-proved). The headline results are three theorems
about the whole grid, each a postcondition with a `forall`:

- filling never lowers the ground: `fill.[k] >= dem.[k]` for every cell;
- every flow direction points strictly downhill, or nowhere;
- no cell's accumulation exceeds the number of cells, and every watershed
  label is an outlet;
- sediment transport conserves the total mass exactly:
  `sum bed + sum load + sum inflow + gone` never changes.

The second one is what makes the third possible: because water only ever
runs strictly downhill, the path from a cell must end, and it cannot visit a
cell twice.

## The grid

The heights arrive as a slice of `u16`, one per cell, stored row by row,
`w` cells to a row. So the cell above cell `m` is `m - w`, and the one below
is `m + w`. The first and last rows and columns are the *border*: water that
reaches a border cell leaves the map. Every loop over the grid visits the
*interior* the same way the [edge detector](demo.md) does: a row at a time,
starting at row offset `r = w`, and keeping one row on each side, so all
eight neighbours of an interior cell are in bounds.

The program never multiplies. A module that multiplies is encoded with much
wider bit-vectors, and loop proofs then time out
([issue #45](https://github.com/deanberris/pia-lang/issues/45)), so it adds
instead: row offsets grow by `w`, and `3 * i` is `i + i + i`.

The file is one module, `Streams` ([ADR 0039](adr/0039-module-and-interface-syntax.md)).
Its interface lists the eight functions the C program calls, with the
preconditions a caller must keep; everything else on this page is private
to the module:

```pia
module Streams : Delineation

interface Delineation @abi(c) = sig
  let fill_sinks : (dem : [u16]) -> (w : usize) -> (limit : u32)
      -> (fill : out mutable [u16]) -> u32
    requires len fill = len dem && w >= 3 && w + w + w <= len dem
  let directions : (fill : [u16]) -> (w : usize)
      -> (down : out mutable [usize]) -> unit
    requires len down = len fill && w >= 3 && w + w + w <= len fill
  let accumulate : (fill : [u16]) -> (down : [usize])
      -> (acc : out mutable [u32]) -> (basin : out mutable [usize]) -> unit
    requires len down = len fill && len acc = len fill && len basin = len fill
    requires len fill < 4294967295
    requires forall (k in 0..len down).
               down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  let render : (dem : [u16]) -> (fill : [u16]) -> (acc : [u32])
      -> (basin : [usize]) -> (threshold : u32) -> (rgb : out mutable [u8])
      -> usize
    requires len fill = len dem && len acc = len dem && len basin = len dem
    requires len rgb = len dem + len dem + len dem
  let delineate : (dem : [u16]) -> (w : usize) -> (limit : u32)
      -> (threshold : u32) -> (fill : out mutable [u16])
      -> (down : out mutable [usize]) -> (acc : out mutable [u32])
      -> (basin : out mutable [usize]) -> (rgb : out mutable [u8]) -> usize
    requires w >= 3 && w + w + w <= len dem && len dem < 4294967295
    requires len fill = len dem && len down = len dem && len acc = len dem
    requires len basin = len dem && len rgb = len dem + len dem + len dem
  let palette : (pal : out mutable [u8]) -> unit
    requires len pal = 768
  let render_load_index : (dem : [u16]) -> (fill : [u16]) -> (acc : [u32])
      -> (basin : [usize]) -> (flux : [u32]) -> (threshold : u32)
      -> (idx : out mutable [u8]) -> unit
    requires len fill = len dem && len acc = len dem && len basin = len dem
    requires len flux = len dem && len idx = len dem
  let render_load : (dem : [u16]) -> (fill : [u16]) -> (acc : [u32])
      -> (basin : [usize]) -> (flux : [u32]) -> (threshold : u32)
      -> (rgb : out mutable [u8]) -> usize
    requires len fill = len dem && len acc = len dem && len basin = len dem
    requires len flux = len dem && len rgb = len dem + len dem + len dem
end
```

Heights are compared through two small helpers whose postconditions say
exactly what they return, so callers can reason about the result:

```pia
let lower (a : u16) (b : u16) : u16
  ensures result <= a && result <= b && (result = a || result = b)
= if a < b then a else b
```

`higher` is its mirror image.

```pia
let higher (a : u16) (b : u16) : u16
  ensures result >= a && result >= b && (result = a || result = b)
= if a > b then a else b
```

The lowest of the eight neighbours of cell `m`, which is in the interior
of the row that starts at `r`. Every function that looks at a cell's
neighbours takes this precondition, *row form*: `r` is an interior row
(`w <= r` and another row fits below it) and `m` is neither its first
cell nor its last. It is exactly what a loop over the row knows, and it
gives the bounds of all eight reads.

```pia
let lowest_around (fill : [u16]) (w : usize) (r : usize) (m : usize) : u16
  requires w <= r && r + w + w <= len fill && r < m && m + 1 < r + w
=
  assert w < m && m + w + 1 < len fill;
  let a = m - w in
  let b = m + w in
  let above = lower (lower (fill.[a - 1]) (fill.[a])) (fill.[a + 1]) in
  let beside = lower (fill.[m - 1]) (fill.[m + 1]) in
  let below = lower (lower (fill.[b - 1]) (fill.[b])) (fill.[b + 1]) in
  lower (lower above beside) below
```

The offset of the last interior row: the last row that has a row after it.
The loop walks down the rows; its measure is the distance to the end of the
slice, which shrinks by `w` each time.

```pia
let last_row (n : usize) (w : usize) : usize
  requires w >= 3 && w + w + w <= n
  ensures w <= result && result + w + w <= n
=
  let r : mutable usize = w in
  while w <= n - (r + w + w)
    invariant w <= r && r + w + w <= n
    decreases n - r
  do
    r <- r + w
  done;
  r
```

## 1. Filling sinks

The method is Planchon and Darboux's
([2001](https://doi.org/10.1016/S0341-8162(01)00164-3)). Start from a
surface `fill` that equals the terrain on the border and is as high as
possible everywhere else, as if the map were flooded. Then let the water
drain: each interior cell is lowered to

```text
higher (dem.[m]) (lowest_around fill w r m + 1)
```

that is, to the ground if the ground already sits above a neighbour, and
otherwise to just one unit above its lowest neighbour. Repeat until nothing
changes. A pit ends up level with the point where it spills, plus one unit
per cell back from that point, so even a filled lake slopes gently towards
its outlet and the next stage always finds a way down. The `+ 1` saturates
(`+|`) at 65535, so heights near the top of the range cannot overflow; a
cell there may simply find no lower neighbour, which the later stages
handle.

`settle` lowers one cell and says whether it changed. Its contract carries
the first theorem through the whole stage: if no cell of `fill` is below the
ground before, none is after. That holds because the new value is the lower
of the old value and a value above the ground, and `lower` returns one of
its arguments.

```pia
let settle (dem : [u16]) (w : usize) (r : usize) (m : usize)
    (fill : inout mutable [u16]) : bool
  requires len fill = len dem
  requires w <= r && r + w + w <= len fill && r < m && m + 1 < r + w
  requires forall (k in 0..len fill). fill.[k] >= dem.[k]
  ensures forall (k in 0..len fill). fill.[k] >= dem.[k]
=
  let here = fill.[m] in
  let spill = higher (dem.[m]) (lowest_around fill w r m +| 1) in
  fill.[m] <- lower spill here;
  spill < here
```

Settles the interior of the row that starts at `r`, left to right. Each
cell sees the new values of the cells before it, which is why the method
converges in few sweeps (a Gauss-Seidel iteration), and also why this loop
cannot be vectorised: each cell depends on the one just written. The loop
runs over the cell offsets `m` themselves, so its bounds are `settle`'s
row-form precondition. The call comes before `||`, so it runs even once
`changed` is true.

```pia
let settle_row (dem : [u16]) (w : usize) (r : usize)
    (fill : inout mutable [u16]) : bool
  requires len fill = len dem && w >= 3 && w <= r && r + w + w <= len fill
  requires forall (k in 0..len fill). fill.[k] >= dem.[k]
  ensures forall (k in 0..len fill). fill.[k] >= dem.[k]
=
  let changed : mutable bool = false in
  for m in r + 1..r + w - 1
    invariant forall (k in 0..len fill). fill.[k] >= dem.[k]
  do
    changed <- settle dem w r m fill || changed
  done;
  changed
```

The same, right to left. Water can only travel against the direction of a
sweep one cell per sweep, so sweeps alternate direction.

```pia
let settle_row_back (dem : [u16]) (w : usize) (r : usize)
    (fill : inout mutable [u16]) : bool
  requires len fill = len dem && w >= 3 && w <= r && r + w + w <= len fill
  requires forall (k in 0..len fill). fill.[k] >= dem.[k]
  ensures forall (k in 0..len fill). fill.[k] >= dem.[k]
=
  let changed : mutable bool = false in
  for i in 0..w - 2
    invariant forall (k in 0..len fill). fill.[k] >= dem.[k]
  do
    changed <- settle dem w r (r + w - 2 - i) fill || changed
  done;
  changed
```

One sweep over the interior rows, top to bottom. This loop is the edge
detector's: the condition says another row fits below this one, and the
measure is the distance to the end.

```pia
let sweep_down (dem : [u16]) (w : usize) (fill : inout mutable [u16]) : bool
  requires len fill = len dem && w >= 3 && w + w + w <= len fill
  requires forall (k in 0..len fill). fill.[k] >= dem.[k]
  ensures forall (k in 0..len fill). fill.[k] >= dem.[k]
=
  let changed : mutable bool = false in
  let r : mutable usize = w in
  while w <= len fill - (r + w)
    invariant w <= r && r + w <= len fill
    invariant forall (k in 0..len fill). fill.[k] >= dem.[k]
    decreases len fill - r
  do
    changed <- settle_row_back dem w r fill || changed;
    r <- r + w
  done;
  changed
```

One sweep bottom to top, from the last interior row. `next` is the offset
of the row after the one being settled, so the loop stops after row `w`
without `r` ever going below it.

```pia
let sweep_up (dem : [u16]) (w : usize) (last : usize)
    (fill : inout mutable [u16]) : bool
  requires len fill = len dem && w >= 3 && w <= last && last + w + w <= len fill
  requires forall (k in 0..len fill). fill.[k] >= dem.[k]
  ensures forall (k in 0..len fill). fill.[k] >= dem.[k]
=
  let changed : mutable bool = false in
  let next : mutable usize = last + w in
  while next >= w + w
    invariant next + w <= len fill
    invariant forall (k in 0..len fill). fill.[k] >= dem.[k]
    decreases next
  do
    changed <- settle_row dem w (next - w) fill || changed;
    next <- next - w
  done;
  changed
```

Floods the interior of the row that starts at `r`: the starting surface.
The flood level is written `higher (dem.[m]) 65535`, which is always
65535, because the verifier does not yet know that a `u16` read from a
slice inside a `forall` is at most 65535
([issue #96](https://github.com/deanberris/pia-lang/issues/96)).
`higher`'s postcondition says it is not below the ground.

```pia
let flood_row (dem : [u16]) (w : usize) (r : usize)
    (fill : inout mutable [u16]) : unit
  requires len fill = len dem && w >= 3 && w <= r && r + w + w <= len fill
  requires forall (k in 0..len fill). fill.[k] >= dem.[k]
  ensures forall (k in 0..len fill). fill.[k] >= dem.[k]
=
  for m in r + 1..r + w - 1
    invariant forall (k in 0..len fill). fill.[k] >= dem.[k]
  do
    fill.[m] <- higher (dem.[m]) 65535
  done
```

The whole stage. It copies the terrain, floods the interior, then sweeps
down and up until a pair of sweeps changes nothing, or `limit` pairs have
run. It returns the number of pairs. The loop's measure is the number of
pairs left, so it ends even on a terrain that would take longer to settle;
when the result is `limit`, the surface may not have settled, and the later
stages are still correct on it, only less useful. The `ensures` is the
first theorem: the filled surface is nowhere below the ground. The copy
loop is a straight copy, which LLVM turns into NEON loads and stores.

```pia
let fill_sinks (dem : [u16]) (w : usize) (limit : u32)
    (fill : out mutable [u16]) : u32
  requires len fill = len dem && w >= 3 && w + w + w <= len dem
  ensures forall (k in 0..len fill). fill.[k] >= dem.[k]
  ensures result <= limit
=
  for i in 0..len dem
    invariant forall (k in 0..i). fill.[k] >= dem.[k]
  do
    fill.[i] <- dem.[i]
  done;
  let r : mutable usize = w in
  while w <= len fill - (r + w)
    invariant w <= r && r + w <= len fill
    invariant forall (k in 0..len fill). fill.[k] >= dem.[k]
    decreases len fill - r
  do
    flood_row dem w r fill;
    r <- r + w
  done;
  let last = last_row (len fill) w in
  let passes : mutable u32 = 0 in
  let changed : mutable bool = true in
  while changed && passes < limit
    invariant passes <= limit
    invariant forall (k in 0..len fill). fill.[k] >= dem.[k]
    decreases limit - passes
  do
    let downwards = sweep_down dem w fill in
    let upwards = sweep_up dem w last fill in
    changed <- downwards || upwards;
    passes <- passes + 1
  done;
  passes
```

## 2. D8 flow directions

D8 sends all the water on a cell to one of its eight neighbours, the one
down the steepest slope. A diagonal neighbour is √2 times as far away as
one beside or above, so its drop counts for less: drops are weighted by 10
for the four near neighbours and by 7 for the diagonals, since 10/√2 is
7.07. A cell with no lower neighbour, such as an outlet on the border,
points at itself.

The direction of a cell is stored as the index of the cell it drains to, in
a slice `down`. The property that matters downstream is that every
direction points *strictly downhill*:

```text
down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
```

The verifier proves this for every cell, starting with one candidate at a
time. A `route` is the best neighbour found so far, with its weighted drop.

```pia
let route = type { target : usize; drop : u32 }
```

Ten times a drop, by addition.

```pia
let tenfold (d : u16) : u32 =
  let d2 : u32 = d + d in
  let d4 : u32 = d2 + d2 in
  d4 + d4 + d2
```

Seven times a drop.

```pia
let sevenfold (d : u16) : u32 =
  let d2 : u32 = d + d in
  let d4 : u32 = d2 + d2 in
  d4 + d2 + d
```

Considers neighbour `n` of cell `m` against the best route so far. A
neighbour wins only if it is lower than `m` and its weighted drop beats the
best, so ties go to the first neighbour considered. Whatever happens, the
route still points at `m` itself or strictly downhill: the precondition
says so of `best`, and the postcondition of the result.

```pia
let consider (fill : [u16]) (m : usize) (n : usize) (diagonal : bool)
    (best : route) : route
  requires m < len fill && n < len fill
  requires best.target = m
           || (best.target < len fill && fill.[best.target] < fill.[m])
  ensures result.target = m
          || (result.target < len fill && fill.[result.target] < fill.[m])
=
  if fill.[n] < fill.[m] then
    (let d : u16 = fill.[m] - fill.[n] in
     let slope : u32 = if diagonal then sevenfold d else tenfold d in
     if slope > best.drop then { target = n; drop = slope } else best)
  else best
```

The D8 direction of interior cell `m`: the eight neighbours, row by row.

```pia
let steepest (fill : [u16]) (w : usize) (r : usize) (m : usize) : usize
  requires w <= r && r + w + w <= len fill && r < m && m + 1 < r + w
  ensures result = m || (result < len fill && fill.[result] < fill.[m])
=
  assert w < m && m + w + 1 < len fill;
  let a = m - w in
  let b = m + w in
  let none : route = { target = m; drop = 0 } in
  let r1 = consider fill m (a - 1) true none in
  let r2 = consider fill m a false r1 in
  let r3 = consider fill m (a + 1) true r2 in
  let r4 = consider fill m (m - 1) false r3 in
  let r5 = consider fill m (m + 1) false r4 in
  let r6 = consider fill m (b - 1) true r5 in
  let r7 = consider fill m b false r6 in
  let r8 = consider fill m (b + 1) true r7 in
  r8.target
```

The directions of the interior of the row that starts at `r`. The loop
invariant is the downhill property for the whole slice: writing one cell's
direction keeps it, because `steepest` guarantees it for that cell.

```pia
let directions_row (fill : [u16]) (w : usize) (r : usize)
    (down : inout mutable [usize]) : unit
  requires len down = len fill && w >= 3 && w <= r && r + w + w <= len fill
  requires forall (k in 0..len down).
             down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  ensures forall (k in 0..len down).
            down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
=
  for m in r + 1..r + w - 1
    invariant forall (k in 0..len down).
                down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  do
    down.[m] <- steepest fill w r m
  done
```

The whole stage. Every cell starts pointing at itself, which is trivially
"downhill or nowhere", so border cells are outlets; then each interior row
gets its directions. The row loop counts up to the last interior row
rather than testing for room below, as the others do: with the downhill
`forall` in its invariant, the solver could not see the subtraction in that
test was safe within its timeout
([issue #96](https://github.com/deanberris/pia-lang/issues/96)), and
comparisons with `last` need no subtraction. The postcondition is the second theorem. Unlike
filling, each cell's direction depends only on `fill`, so the rows are
independent; once `spread` is compiled
([M12](https://github.com/deanberris/pia-lang/issues/13)) they can run in
parallel.

```pia
let directions (fill : [u16]) (w : usize) (down : out mutable [usize]) : unit
  requires len down = len fill && w >= 3 && w + w + w <= len fill
  ensures forall (k in 0..len down).
            down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
=
  for i in 0..len down
    invariant forall (k in 0..i). down.[k] = k
  do
    down.[i] <- i
  done;
  let last = last_row (len fill) w in
  let r : mutable usize = w in
  while r <= last
    invariant w <= r && r <= last + w && last + w + w <= len fill
    invariant forall (k in 0..len down).
                down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
    decreases last + w - r
  do
    directions_row fill w r down;
    r <- r + w
  done
```

## 3. Flow accumulation and watersheds

The flow accumulation of a cell is the number of cells whose water passes
through it, itself included. One way to count it is to start a drop of
water on every cell in turn, follow the directions until it reaches an
outlet, and add one to every cell on the way. The outlet where the drop
ends is the cell's watershed label.

`walk` follows one drop from `start`. Two things about it are proved here
that a C programmer would only argue in a comment.

**It ends.** The loop's measure is the height of the current cell,
`fill.[cur]`. The downhill theorem says each step goes to a strictly lower
cell, so the measure falls every iteration, and a `u16` cannot fall
forever.

**It counts every cell at most once.** Before the walk, no count exceeds
`bound`. The invariant splits the grid by height: cells strictly below the
drop have not been visited yet, so their counts are still at most `bound`,
and every count is at most `bound + 1`. Stepping down to the next cell, it
is below the drop, so its count goes from at most `bound` to at most
`bound + 1`, and the cells below *it* are still below the drop. That is why
the `+ 1` cannot overflow, with no saturation and no run-time check.

```pia
let walk (fill : [u16]) (down : [usize]) (start : usize) (bound : u32)
    (acc : inout mutable [u32]) : usize
  requires len down = len fill && len acc = len fill && start < len fill
  requires bound < 4294967295
  requires forall (k in 0..len down).
             down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0..len acc). acc.[k] <= bound
  ensures result < len fill && down.[result] = result
  ensures forall (k in 0..len acc). acc.[k] <= bound + 1
=
  acc.[start] <- acc.[start] + 1;
  let cur : mutable usize = start in
  while down.[cur] <> cur
    invariant cur < len fill
    invariant forall (k in 0..len acc).
                (fill.[k] < fill.[cur] ==> acc.[k] <= bound) && acc.[k] <= bound + 1
    decreases fill.[cur]
  do
    cur <- down.[cur];
    acc.[cur] <- acc.[cur] + 1
  done;
  cur
```

The whole stage: a walk from every cell. After `s` walks no count exceeds
`s`, so at the end none exceeds the number of cells; and every label
written so far is an outlet, a cell that points at itself. These are the
third theorem. The precondition on `len fill` keeps the counts within
`u32`. Its downhill precondition is exactly the postcondition of
`directions`, which is how the stages compose: each is proved against the
contract of the one before, not its code.

The cost is the total length of all the paths, which is fine for maps of a
few million cells. A faster method visits each cell once in topological
order, but needs a queue the size of the map, and Pia cannot allocate one
yet ([issue #86](https://github.com/deanberris/pia-lang/issues/86)).

```pia
let accumulate (fill : [u16]) (down : [usize]) (acc : out mutable [u32])
    (basin : out mutable [usize]) : unit
  requires len down = len fill && len acc = len fill && len basin = len fill
  requires len fill < 4294967295
  requires forall (k in 0..len down).
             down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  ensures forall (k in 0..len acc). acc.[k] <= len fill
  ensures forall (k in 0..len basin).
            basin.[k] < len fill && down.[basin.[k]] = basin.[k]
=
  for i in 0..len acc
    invariant forall (k in 0..i). acc.[k] = 0
  do
    acc.[i] <- 0
  done;
  for s in 0..len fill
    invariant forall (k in 0..len acc). acc.[k] <= s
    invariant forall (k in 0..s).
                basin.[k] < len fill && down.[basin.[k]] = basin.[k]
  do
    basin.[s] <- walk fill down s s acc
  done
```

## 4. Streams and the picture

A cell is on a stream when at least `threshold` cells drain through it.
The picture shows streams in blue, darker where the flow is at least 16
times the threshold; cells that filling raised, the lakes, in pale blue;
and everything else in its watershed's colour, darker where it is lower.
Neighbouring watersheds can share one of the six colours, since the palette
cycles by outlet index.

```pia
let colour = type { red : u8; green : u8; blue : u8 }
```

The colour of watershed `outlet`.

```pia
let tint (outlet : usize) : colour =
  let k = outlet mod 6 in
  if k = 0 then { red = 214; green = 168; blue = 110 }
  else if k = 1 then { red = 150; green = 190; blue = 110 }
  else if k = 2 then { red = 200; green = 140; blue = 160 }
  else if k = 3 then { red = 120; green = 170; blue = 160 }
  else if k = 4 then { red = 210; green = 200; blue = 120 }
  else { red = 170; green = 150; blue = 200 }
```

Whether flow `a` is at least sixteen times `threshold`, in `u64` so the
product cannot overflow.

```pia
let major (a : u32) (threshold : u32) : bool =
  let t2 : u64 = threshold + threshold in
  let t4 : u64 = t2 + t2 in
  let t8 : u64 = t4 + t4 in
  a >= t8 + t8
```

The colour of one cell: its height `h` before and `f` after filling, its
flow `a`, and its watershed. A height is 0 to 65535, so `h / 256` is a
byte, and the average of a byte and a byte is a byte: the verifier proves
both narrowings.

```pia
let paint (h : u16) (f : u16) (a : u32) (outlet : usize) (threshold : u32)
    : colour =
  if a >= threshold then
    (if major a threshold then { red = 20; green = 70; blue = 190 }
     else { red = 70; green = 140; blue = 240 })
  else if f > h then { red = 150; green = 205; blue = 235 }
  else
    (let t = tint outlet in
     let shade : u16 = h / 256 in
     let r : u16 = t.red + shade in
     let g : u16 = t.green + shade in
     let b : u16 = t.blue + shade in
     { red = r / 2; green = g / 2; blue = b / 2 })
```

The picture, as packed RGB bytes, and the number of stream cells, which
the invariant bounds by the number of cells painted.

```pia
let render (dem : [u16]) (fill : [u16]) (acc : [u32]) (basin : [usize])
    (threshold : u32) (rgb : out mutable [u8]) : usize
  requires len fill = len dem && len acc = len dem && len basin = len dem
  requires len rgb = len dem + len dem + len dem
  ensures result <= len dem
=
  let streams : mutable usize = 0 in
  for i in 0..len dem
    invariant streams <= i
  do
    let c = paint (dem.[i]) (fill.[i]) (acc.[i]) (basin.[i]) threshold in
    let j = i + i + i in
    rgb.[j] <- c.red;
    rgb.[j + 1] <- c.green;
    rgb.[j + 2] <- c.blue;
    streams <- streams + (if acc.[i] >= threshold then 1 else 0)
  done;
  streams
```

## The whole pipeline

`delineate` runs the four stages and returns the number of stream cells.
Each call's precondition is proved from the caller's own and from the
postconditions of the calls before it; in particular `accumulate` needs
the downhill theorem, which only `directions` provides. Swap the two calls
and the program no longer compiles.

```pia
let delineate (dem : [u16]) (w : usize) (limit : u32) (threshold : u32)
    (fill : out mutable [u16]) (down : out mutable [usize])
    (acc : out mutable [u32]) (basin : out mutable [usize])
    (rgb : out mutable [u8]) : usize
  requires w >= 3 && w + w + w <= len dem && len dem < 4294967295
  requires len fill = len dem && len down = len dem && len acc = len dem
  requires len basin = len dem && len rgb = len dem + len dem + len dem
  ensures result <= len dem
=
  let passes = fill_sinks dem w limit fill in
  directions fill w down;
  accumulate fill down acc basin;
  render dem fill acc basin threshold rgb
```

## 5. Sediment transport

The second half of the demo moves sediment down the streams, and is its
own page and module, [sediment.pia.md](sediment.pia.md), so the two prove
in parallel. Its entry point takes the filled heights, the directions and
the accumulation from this page, and returns `flux`, the load leaving each
cell. This page draws it.

The colour of a stream cell by the load leaving it: a ramp over the binary
logarithm of the load, from blue for 63 units or fewer to orange for 8192
or more, in eight steps. `clz` counts the leading zeros, so 32 - clz f is
the number of bits in f, with no logarithm and no multiplication.

```pia
let load_colour (f : u32) : colour =
  let lz : u32 = clz f in
  let l : u32 = 32 - lz in
  let m : u32 = if l < 6 then 0 else if l > 13 then 7 else l - 6 in
  { red = 31 + (m << 5); green = 60 + (m << 4); blue = 230 - (m << 5) }
```

The picture after transport: stream cells coloured by their load, every
other cell as in `render`.

```pia
let render_load (dem : [u16]) (fill : [u16]) (acc : [u32]) (basin : [usize])
    (flux : [u32]) (threshold : u32) (rgb : out mutable [u8]) : usize
  requires len fill = len dem && len acc = len dem && len basin = len dem
  requires len flux = len dem && len rgb = len dem + len dem + len dem
  ensures result <= len dem
=
  let streams : mutable usize = 0 in
  for i in 0..len dem
    invariant streams <= i
  do
    let c = (if acc.[i] >= threshold then load_colour (flux.[i])
             else paint (dem.[i]) (fill.[i]) (acc.[i]) (basin.[i]) threshold) in
    let j = i + i + i in
    rgb.[j] <- c.red;
    rgb.[j + 1] <- c.green;
    rgb.[j + 2] <- c.blue;
    streams <- streams + (if acc.[i] >= threshold then 1 else 0)
  done;
  streams
```

## 6. The animation's palette

An animated GIF has one palette for all its frames, so for the evolution's
animation each cell becomes an index into one fixed palette rather than a
colour. `load_step` is the step of the load ramp, as in `load_colour`.

```pia
let load_step (f : u32) : int{0..7} =
  let lz : u32 = clz f in
  let l : u32 = 32 - lz in
  if l < 6 then 0 else if l > 13 then 7 else l - 6
```

The palette index of one cell: the eight steps of the load ramp for
streams, then the lake colour, then the six watershed tints in 32 shades of
height each, 201 colours in all. `outlet mod 6` and `h >> 11` are both
small, so the index is proved to be below 201 by its type.

```pia
let index_of (h : u16) (f : u16) (a : u32) (outlet : usize) (flux : u32)
    (threshold : u32) : int{0..200} =
  if a >= threshold then load_step flux
  else if f > h then 8
  else
    (let k : int{0..5} = outlet mod 6 in
     let s : int{0..31} = h >> 11 in
     9 + (k << 5) + s)
```

The colour of each index: the ramp and the lake as above, and a watershed
shade as `paint` mixes it, with the height taken at the middle of its
shade. Indices from 201 up are unused and black.

```pia
let index_colour (i : u8) : colour =
  if i < 8 then
    (let m : u8 = i in
     { red = 31 + (m << 5); green = 60 + (m << 4); blue = 230 - (m << 5) })
  else if i = 8 then { red = 150; green = 205; blue = 235 }
  else if i < 201 then
    (let j : u8 = i - 9 in
     let t = tint (j >> 5) in
     let shade : u16 = ((j & 31) << 3) + 4 in
     let r : u16 = t.red + shade in
     let g : u16 = t.green + shade in
     let b : u16 = t.blue + shade in
     { red = r / 2; green = g / 2; blue = b / 2 })
  else { red = 0; green = 0; blue = 0 }
```

The shared palette: 256 colours, three bytes each.

```pia
let palette (pal : out mutable [u8]) : unit
  requires len pal = 768
= for i in 0..256 do
    let c = index_colour i in
    let j = i + i + i in
    pal.[j] <- c.red;
    pal.[j + 1] <- c.green;
    pal.[j + 2] <- c.blue
  done
```

One frame of the animation: every cell's palette index, each proved to
name one of the 201 colours `palette` fills.

```pia
let render_load_index (dem : [u16]) (fill : [u16]) (acc : [u32]) (basin : [usize])
    (flux : [u32]) (threshold : u32) (idx : out mutable [u8]) : unit
  requires len fill = len dem && len acc = len dem && len basin = len dem
  requires len flux = len dem && len idx = len dem
  ensures forall (k in 0..len idx). idx.[k] < 201
=
  for i in 0..len dem
    invariant forall (k in 0..i). idx.[k] < 201
  do
    idx.[i] <- index_of (dem.[i]) (fill.[i]) (acc.[i]) (basin.[i]) (flux.[i]) threshold
  done
```

## Why the order matters

Here is the walk without the downhill precondition. Nothing then stops
`down` from containing a cycle, so the loop might never end, and the
verifier says so: the measure is not proved to decrease, and `piac`
refuses to compile it.

<!-- example: walk_unproved.pia -->
<!-- expect: fail -->
```ocaml
let walk (fill : [u16]) (down : [usize]) (start : usize) : usize
  requires len down = len fill && start < len fill
  requires forall (k in 0..len down). down.[k] < len fill
=
  let cur : mutable usize = start in
  while down.[cur] <> cur
    invariant cur < len fill
    decreases fill.[cur]
  do
    cur <- down.[cur]
  done;
  cur
```

```console
$ piac --verify walk_unproved.pia
...
walk_unproved.pia:8:5: failed: the measure decreases
...
```

## What is proved

Every goal in this file is proved, by interval analysis or by Z3, before
`piac` generates code:

| Goal | Where |
| --- | --- |
| Every slice index is in bounds | every function |
| No arithmetic overflows, and every narrowing fits | every function; `walk`'s `+ 1` by its invariant |
| Every loop ends | `for` loops always; `while` loops by `decreases`; `walk` by the height of the drop |
| Filling never lowers the ground | `settle` up to `fill_sinks` |
| Every direction points strictly downhill or nowhere | `consider` up to `directions` |
| Accumulation never exceeds the number of cells | `walk`, `accumulate` |
| Every watershed label is an outlet | `walk`, `accumulate` |
| The number of stream cells is at most the number of cells | `render`, `render_load` |
| Every animation frame's index names one of the palette's 201 colours | `index_of`, `render_load_index` |

What is *not* proved yet: that filling reaches a fixed point within
`limit` sweeps (the result says whether it did), that a fixed point leaves
no interior pits, and that the D8 choice is the steepest, rather than just
downhill. None of these affect safety or termination.

## What is missing

The demo works around parts of Pia that are not built yet:

- **Image I/O.** Pia has no I/O, so [`main.c`](https://github.com/deanberris/pia-lang/blob/main/examples/streams/main.c)
  reads and writes images with macOS's ImageIO and hands Pia the heights.
  PNG and GIF codecs written in Pia are
  [M13](https://github.com/deanberris/pia-lang/issues/14), on top of the
  minimal core ([ADR 0023](adr/0023-minimal-core-self-hosted-stdlib.md)).
- **Allocation.** The caller passes every buffer. With the memory module
  ([issue #86](https://github.com/deanberris/pia-lang/issues/86)),
  `delineate` could allocate its own and use a queue for a linear-time
  accumulation.
- **Multiplication in loops** makes proofs time out
  ([issue #45](https://github.com/deanberris/pia-lang/issues/45)), so the
  code adds instead, and the slope weights are `tenfold` and `sevenfold`.
- **Floats** ([M11](https://github.com/deanberris/pia-lang/issues/12))
  would give true slopes in place of the 10:7 weights.
- **Vectorisation and parallelism.** Today LLVM vectorises only the
  simple loops: the copy in `fill_sinks` and `down.[i] <- i` in
  `directions` become NEON loads, stores and adds. The stencil kernels
  (`settle`, `steepest`) and the walks are scalar. `steepest` and `paint`
  are branch-free enough to vectorise once proved facts drive it
  ([M10](https://github.com/deanberris/pia-lang/issues/11)), and
  `directions` and `render` are independent per row and per cell, so
  `spread` ([M12](https://github.com/deanberris/pia-lang/issues/13)) can
  run them across cores. Gauss-Seidel filling stays sequential by design.
- **Solver robustness.** Goals beside a `forall` are slow for the solver,
  and some slices' element ranges are lost inside quantifiers
  ([issue #96](https://github.com/deanberris/pia-lang/issues/96)); the
  code is shaped around both, as noted where it matters.
