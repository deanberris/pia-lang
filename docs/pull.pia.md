# Demo: sediment in pull form, proved equal to the sequential step

The sediment step of [sediment.pia.md](sediment.pia.md) goes through the
cells in height order, highest first. Each cell erodes or deposits, then
*pushes* its load into the cell below it. That order is sequential: a cell
needs every load pushed into it before it can move. [ADR
0055](adr/0055-sediment-transport-in-fixed-point.md), section 6, plans the
GPU form, a *pull* step. Here every cell reads its eight neighbours and
adds the loads of those that drain into it, so each cell writes only
itself.

This page is that step. The cells are taken in *waves*, one for each
height. A cell's upstream neighbours are strictly higher, so they belong
to earlier waves. Within a wave the cells are independent. So a wave is a
`spread` ([ADR 0060](adr/0060-spread-v0-ownership-and-runtime.md)) with
the default identity ownership. Each iteration writes only its own slots
of three scratch buffers, and a short pass then commits the wave in order.

The theorem is that it is the same step, exactly:

```text
from the same bed, the pull step and the sequential step leave the same
bed and the same load leaving every cell, cell for cell, and send the
same mass off the map.
```

It is `same_step`, at the end of the page, and `both_steps` runs the two
steps and states it as its postcondition. Exact conservation then carries
over from the sequential step, as do the bounds that keep every sum in a
`u32`.

## The proof, in outline

A step is pinned down by what each cell takes in. Call a step *settled*
when every cell's bed and load are what erosion and deposition make of the
inflow it took, `seen.[c]`. Call it *linked* when that inflow is the sum
of the loads leaving those of its eight neighbours that drain into it.
Two settled, linked steps from the same bed are the same step. Take the
cells in height order: a cell's upstream neighbours come before it, so by
its turn they agree, so its inflow does, so it does (`agree`).

So the work is to prove each step settled and linked. For the sequential
step, `transport_seen` keeps three invariants as it goes:

- every processed cell has settled (`done_upto`);
- every processed cell is linked (`linked_upto`);
- every cell not yet processed holds, as its inflow, the loads of exactly
  its processed upstream neighbours (`pending`).

For the pull step, the kernel computes each cell's inflow and result. The
commit pass keeps the same `linked_upto`, and the pull step's own promise
(`holds_if`), as it writes them back. The sums that both steps send off
the map are the outlets' loads, added in height order (`osum`).

The predicates are opaque spec functions ([ADR
0063](adr/0063-opaque-spec-functions.md)), revealed only in small step
lemmas. Without that, a hypothesis that reads `flux` at a cell's
neighbours and one about every cell instantiate each other across the
whole grid, a matching loop. Inflows are trees of two-term sums for the
same reason: under a quantifier, Z3 proves two-term sums equal at once,
and eight-term sums not at all.

The page is its own module. `examples/streams/srtm.c` runs it on a real
tile and checks it against the sequential `sediment` cell for cell.

```pia
module Pull : PullTransport, PullWaves

interface PullTransport @abi(c) = sig
  let pull_step : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (order : [usize])
      -> (pos : [usize]) -> (w : usize) -> (bed0 : [u32])
      -> (bed : borrowed inout mutable [u32]) -> (flux : borrowed inout mutable [u32])
      -> (seen : borrowed inout mutable [u64]) -> (gathered : borrowed inout mutable [u64])
      -> (newbed : borrowed inout mutable [u32]) -> (newout : borrowed inout mutable [u32])
      -> (gone : u64) -> u64
    requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
    requires len bed = len fill && len flux = len fill && len seen = len fill
    requires len gathered = len fill && len newbed = len fill && len newout = len fill
    requires w >= 3 && w < max usize && len fill < max u32 && gone <= max u32
    requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
    requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
    requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
    requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
    requires forall (k in 0 .. len down). down.[k] < len fill
end
```

The page also provides a second interface, `PullWaves`, for the GPU form of
the step in [pull_gpu.pia.md](pull_gpu.pia.md). It is what a step needs to
run its own waves and still be proved: the specification functions its
promise is written in, the commit pass and the lemmas around it. A spec
function is exported with its definition, so every one that a definition
uses is listed too.

```pia
interface PullWaves = sig
  let spec nbr : (n : usize) -> (w : usize) -> (c : usize) -> (d : int{0..7}) -> usize
  let spec from : (down : [usize]) -> (flux : [u32]) -> (w : usize) -> (c : usize) -> (d : int{0..7}) -> u64
  let spec pair : (down : [usize]) -> (flux : [u32]) -> (w : usize) -> (c : usize) -> (h : int{0..3}) -> u64
  let spec half : (down : [usize]) -> (flux : [u32]) -> (w : usize) -> (c : usize) -> (g : int{0..1}) -> u64
  let spec inflow_of : (down : [usize]) -> (flux : [u32]) -> (w : usize) -> (c : usize) -> u64
  let spec el : (i : u64) -> (cap : u32) -> (bed : u32) -> u64
  let spec eb : (i : u64) -> (cap : u32) -> (bed : u32) -> u64
  let spec cap_rule : (a : u32) -> (drop : u16) -> u32
  let spec cap_of : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (c : usize) -> u32
  let spec at : (xs : [usize]) -> (k : usize) -> usize
  let spec holds_if : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (bed0 : [u32]) -> (bed : [u32])
      -> (flux : [u32]) -> (seen : [u64]) -> (c : usize) -> bool
  let spec done_if_upto : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (bed0 : [u32]) -> (bed : [u32])
      -> (flux : [u32]) -> (seen : [u64]) -> (pos : [usize]) -> (p : usize) -> bool
  let spec linked_upto : (down : [usize]) -> (flux : [u32]) -> (seen : [u64]) -> (pos : [usize]) -> (p : usize)
      -> (w : usize) -> bool
  let spec ready_in : (down : [usize]) -> (order : [usize]) -> (w : usize) -> (flux : [u32]) -> (gathered : [u64])
      -> (q : usize) -> (hi : usize) -> bool
  let spec ready_vals : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (order : [usize]) -> (bed0 : [u32])
      -> (gathered : [u64]) -> (newbed : [u32]) -> (newout : [u32]) -> (q : usize) -> (hi : usize) -> bool
  let spec settled_if : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (bed0 : [u32]) -> (bed : [u32])
      -> (flux : [u32]) -> (seen : [u64]) -> bool
  let spec linked : (down : [usize]) -> (flux : [u32]) -> (seen : [u64]) -> (w : usize) -> bool
  let spec oterm : (order : [usize]) -> (down : [usize]) -> (flux : [u32]) -> (q : usize) -> u32
  let spec osum : (order : [usize]) -> (down : [usize]) -> (flux : [u32]) -> (p : usize) -> u64
  let lemma osum_next : (order : [usize]) -> (down : [usize]) -> (flux : [u32]) -> (p : usize) -> unit
    requires p < max u32 + 1
    ensures osum order down flux (p + 1) = osum order down flux p + oterm order down flux p
  let lemma ready_init : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (order : [usize]) -> (w : usize)
      -> (bed0 : [u32]) -> (flux : [u32]) -> (gathered : [u64]) -> (newbed : [u32]) -> (newout : [u32])
      -> (lo : usize) -> (hi : usize) -> unit
    requires len down = len fill && len acc = len fill && len order = len fill && len bed0 = len fill && len flux = len fill
    requires len gathered = len fill && len newbed = len fill && len newout = len fill && hi <= len fill
    requires forall (r in 0 .. len order). order.[r] < len fill
    requires w >= 3 && w < max usize
    requires forall (q in lo .. hi). gathered.[q] = inflow_of down flux w (order.[q])
    requires forall (q in lo .. hi). gathered.[q] + bed0.[order.[q]] <= max u32 ==>
      newbed.[q] = eb (gathered.[q]) (cap_of fill down acc (order.[q])) (bed0.[order.[q]])
      && newout.[q] = el (gathered.[q]) (cap_of fill down acc (order.[q])) (bed0.[order.[q]])
    ensures ready_in down order w flux gathered lo hi
    ensures ready_vals fill down acc order bed0 gathered newbed newout lo hi
  let lemma start_pull : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (bed0 : [u32]) -> (bed : [u32])
      -> (flux : [u32]) -> (seen : [u64]) -> (pos : [usize]) -> (w : usize) -> unit
    requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill
    requires len seen = len fill && len pos = len fill && w >= 3 && w < max usize
    ensures done_if_upto fill down acc bed0 bed flux seen pos 0
    ensures linked_upto down flux seen pos 0 w
  let lemma finish_pull : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (bed0 : [u32]) -> (bed : [u32])
      -> (flux : [u32]) -> (seen : [u64]) -> (pos : [usize]) -> (w : usize) -> unit
    requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill
    requires len seen = len fill && len pos = len fill && w >= 3 && w < max usize
    requires forall (k in 0 .. len pos). pos.[k] < len fill
    requires done_if_upto fill down acc bed0 bed flux seen pos (len fill)
    requires linked_upto down flux seen pos (len fill) w
    ensures settled_if fill down acc bed0 bed flux seen
    ensures linked down flux seen w
  let copy_back : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (order : [usize]) -> (pos : [usize])
      -> (w : usize) -> (bed0 : [u32]) -> (gathered : [u64]) -> (newbed : [u32]) -> (newout : [u32])
      -> (bed : borrowed inout mutable [u32]) -> (flux : borrowed inout mutable [u32])
      -> (seen : borrowed inout mutable [u64]) -> (lo : usize) -> (hi : usize) -> (v : u16) -> (g : u64)
      -> (g0 : u64) -> u64
    requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
    requires len gathered = len fill && len newbed = len fill && len newout = len fill
    requires len bed = len fill && len flux = len fill && len seen = len fill
    requires w >= 3 && w < max usize && lo <= hi && hi <= len fill
    requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
    requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
    requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
    requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
    requires forall (k in 0 .. len down). down.[k] < len fill
    requires forall (r in lo .. hi). fill.[at order r] = v
    requires done_if_upto fill down acc bed0 bed flux seen pos lo
    requires linked_upto down flux seen pos lo w
    requires ready_in down order w flux gathered lo hi
    requires ready_vals fill down acc order bed0 gathered newbed newout lo hi
    requires len fill < max u32 && g0 <= max u32 && g = g0 + osum order down flux lo
    ensures result = g0 + osum order down flux hi
    ensures done_if_upto fill down acc bed0 bed flux seen pos hi
    ensures linked_upto down flux seen pos hi w
  let wave_end : (fill : [u16]) -> (order : [usize]) -> (lo : usize) -> usize
    requires len order = len fill && lo < len fill
    requires forall (r in 0 .. len order). order.[r] < len fill
    ensures lo < result && result <= len fill
    ensures forall (r in lo .. result). fill.[at order r] = fill.[order.[lo]]
end
```

## 1. Neighbours and inflow

A neighbour is one of eight offsets away: `a` comes before `b`, one cell or about one row apart. The check is in `usize`, with no overflow.

```pia
let spec step_of (w : usize) (a : usize) (b : usize) : bool
  requires w >= 1 && w < max usize
= if a < b then (b - a = 1 || b - a = w - 1 || b - a = w || b - a = w + 1) else false
```

`k` and `p` are neighbours.

```pia
let spec adjacent (w : usize) (k : usize) (p : usize) : bool
  requires w >= 1 && w < max usize
= step_of w p k || step_of w k p
```

The neighbour of `c` in direction `d` (row order), or `n` if it is off the slice. It is total, with its guards inside, so that it can sit under a quantifier without a precondition to prove.

```pia
let spec nbr (n : usize) (w : usize) (c : usize) (d : int{0..7}) : usize
= if w < 3 || w = max usize || c >= n then n
  else if d = 0 then (if c >= w + 1 then c - (w + 1) else n)
  else if d = 1 then (if c >= w then c - w else n)
  else if d = 2 then (if c >= w - 1 then c - (w - 1) else n)
  else if d = 3 then (if c >= 1 then c - 1 else n)
  else if d = 4 then (if 1 < n - c then c + 1 else n)
  else if d = 5 then (if w - 1 < n - c then c + (w - 1) else n)
  else if d = 6 then (if w < n - c then c + w else n)
  else (if w + 1 < n - c then c + (w + 1) else n)
```

What neighbour `d` of `c` sends into `c`: its load, if it drains into `c`. Opaque: only the per-direction lemmas see its body.

```pia
let spec from (down : [usize]) (flux : [u32]) (w : usize) (c : usize) (d : int{0..7}) : u64 @opaque
  ensures result <= max u32
= let nb = nbr (len down) w c d in
  if nb < len down && nb < len flux then (if nb <> c && down.[nb] = c then flux.[nb] else 0) else 0
```

Two directions' terms.

```pia
let spec pair (down : [usize]) (flux : [u32]) (w : usize) (c : usize) (h : int{0..3}) : u64
  ensures result <= 8'589'934'590
= if h = 0 then from down flux w c 0 + from down flux w c 1
  else if h = 1 then from down flux w c 2 + from down flux w c 3
  else if h = 2 then from down flux w c 4 + from down flux w c 5
  else from down flux w c 6 + from down flux w c 7
```

Four directions' terms.

```pia
let spec half (down : [usize]) (flux : [u32]) (w : usize) (c : usize) (g : int{0..1}) : u64
  ensures result <= 17'179'869'180
= if g = 0 then pair down flux w c 0 + pair down flux w c 1 else pair down flux w c 2 + pair down flux w c 3
```

Everything `c`'s upstream neighbours send it. It is a tree of two-term sums: under a quantifier, Z3 proves an equality of two-term sums quickly and an equality of eight-term sums not at all. Opaque, so that the frame lemmas can instantiate it as one term.

```pia
let spec inflow_of (down : [usize]) (flux : [u32]) (w : usize) (c : usize) : u64 @opaque
  ensures result <= 34'359'738'360
= half down flux w c 0 + half down flux w c 1
```

The load leaving a cell with inflow `i`, capacity `cap` and bed `bed`: what `erode_or_deposit` computes, as a spec function, total in `i`.

```pia
let spec el (i : u64) (cap : u32) (bed : u32) : u64
= if i > 34'359'738'360 then 0 else if i < cap then (if cap - i < bed then cap else i + bed) else cap
```

The bed it leaves.

```pia
let spec eb (i : u64) (cap : u32) (bed : u32) : u64
= if i > 34'359'738'360 then 0 else if i < cap then (if cap - i < bed then bed - (cap - i) else 0) else bed + (i - cap)
```

`capacity_of`, as a spec function.

```pia
let spec cap_rule (a : u32) (drop : u16) : u32
= let d : u64 = drop in
  let c : u64 = (a >> 4) + (d << 2) in
  if c < max u16 then c else max u16
```

Cell `c`'s capacity, from its flow and its drop, total like `nbr`.

```pia
let spec cap_of (fill : [u16]) (down : [usize]) (acc : [u32]) (c : usize) : u32
= if c < len fill && c < len down && c < len acc then
    (let d = down.[c] in
     if d < len fill then cap_rule (acc.[c]) (if d <> c && fill.[d] < fill.[c] then fill.[c] - fill.[d] else 0)
     else 0)
  else 0
```

Cell `c` has settled: `seen.[c]` is the inflow it took, which fits with its bed in a `u32`, and its bed and load are what erosion and deposition make of them.

```pia
let spec holds (fill : [u16]) (down : [usize]) (acc : [u32]) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) (c : usize) : bool
  requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill && len seen = len fill
  requires c < len fill && down.[c] < len fill
= if seen.[c] > max u32 then false
  else if seen.[c] + bed0.[c] > max u32 then false
  else bed.[c] = eb (seen.[c]) (cap_of fill down acc c) (bed0.[c])
       && flux.[c] = el (seen.[c]) (cap_of fill down acc c) (bed0.[c])
```

A `usize` element read through a spec function, so that the read keeps its range inside a quantifier ([#330](https://github.com/deanberris/pia-lang/issues/330)).

```pia
let spec at (xs : [usize]) (k : usize) : usize
  requires k < len xs
= xs.[k]
```

The partial inflow: what neighbour `d` of `k` sends into `k`, counted only if it was processed before position `p` of the height order.

```pia
let spec pterm (down : [usize]) (flux : [u32]) (pos : [usize]) (p : usize) (w : usize) (k : usize) (d : int{0..7}) : u64 @opaque
  ensures result <= max u32
= let nb = nbr (len down) w k d in
  if nb < len down && nb < len flux && nb < len pos then (if nb <> k && down.[nb] = k && at pos nb < p then flux.[nb] else 0) else 0
```

Two directions of the partial inflow.

```pia
let spec ppair (down : [usize]) (flux : [u32]) (pos : [usize]) (p : usize) (w : usize) (k : usize) (h : int{0..3}) : u64
  ensures result <= 8'589'934'590
= if h = 0 then pterm down flux pos p w k 0 + pterm down flux pos p w k 1
  else if h = 1 then pterm down flux pos p w k 2 + pterm down flux pos p w k 3
  else if h = 2 then pterm down flux pos p w k 4 + pterm down flux pos p w k 5
  else pterm down flux pos p w k 6 + pterm down flux pos p w k 7
```

Four directions of it.

```pia
let spec phalf (down : [usize]) (flux : [u32]) (pos : [usize]) (p : usize) (w : usize) (k : usize) (g : int{0..1}) : u64
  ensures result <= 17'179'869'180
= if g = 0 then ppair down flux pos p w k 0 + ppair down flux pos p w k 1 else ppair down flux pos p w k 2 + ppair down flux pos p w k 3
```

All of it.

```pia
let spec pinflow (down : [usize]) (flux : [u32]) (pos : [usize]) (p : usize) (w : usize) (k : usize) : u64
  ensures result <= 34'359'738'360
= phalf down flux pos p w k 0 + phalf down flux pos p w k 1
```

## 2. Lemmas about the inflow

In the height order a cell's downstream neighbour comes after it ([sediment.pia.md](sediment.pia.md), section 7).

```pia
let lemma later (fill : [u16]) (order : [usize]) (pos : [usize]) (c : usize) (d : usize) : unit
  requires len order = len fill && len pos = len fill && c < len fill && d < len fill
  requires forall (q in 0 .. len order). order.[q] < len pos && pos.[order.[q]] = q
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires fill.[d] < fill.[c]
  ensures pos.[c] < pos.[d]
= let a = pos.[c] in
  let b = pos.[d] in
  assert order.[a] = c && order.[b] = d;
  assert b < a ==> fill.[order.[a]] <= fill.[order.[b]]
```

One direction of `all_in`.

```pia
let lemma all_in_dir (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) (flux : [u32]) (w : usize) (k : usize) (p : usize) (d : int{0..7}) : unit
  requires len down = len fill && len order = len fill && len pos = len fill && len flux = len fill
  requires k < len fill && w >= 3 && w < max usize && pos.[k] <= p
  requires forall (q in 0 .. len order). order.[q] < len pos && pos.[order.[q]] = q
  requires forall (j in 0 .. len pos). pos.[j] < len order && order.[pos.[j]] = j
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (j in 0 .. len down). down.[j] = j || (down.[j] < len fill && fill.[down.[j]] < fill.[j])
  ensures pterm down flux pos p w k d = from down flux w k d
  with from, pterm
= let nb = nbr (len fill) w k d in
  if nb < len fill then (if nb <> k && down.[nb] = k then later fill order pos nb k else ()) else ()
```

Once every upstream neighbour of k is processed, the partial inflow is the inflow.

```pia
let lemma all_in (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) (flux : [u32]) (w : usize) (k : usize) (p : usize) : unit
  requires len down = len fill && len order = len fill && len pos = len fill && len flux = len fill
  requires k < len fill && w >= 3 && w < max usize && pos.[k] <= p
  requires forall (q in 0 .. len order). order.[q] < len pos && pos.[order.[q]] = q
  requires forall (j in 0 .. len pos). pos.[j] < len order && order.[pos.[j]] = j
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (j in 0 .. len down). down.[j] = j || (down.[j] < len fill && fill.[down.[j]] < fill.[j])
  ensures pinflow down flux pos p w k = inflow_of down flux w k
  with inflow_of
= all_in_dir fill down order pos flux w k p 0;
  all_in_dir fill down order pos flux w k p 1;
  all_in_dir fill down order pos flux w k p 2;
  all_in_dir fill down order pos flux w k p 3;
  all_in_dir fill down order pos flux w k p 4;
  all_in_dir fill down order pos flux w k p 5;
  all_in_dir fill down order pos flux w k p 6;
  all_in_dir fill down order pos flux w k p 7
```

Changing flux at `c` changes no direction's term of a cell other than `down.[c]` and `c` itself.

```pia
let lemma frame_dir (down : [usize]) (flux : [u32]) (flux2 : [u32]) (w : usize) (c : usize) (d : int{0..7}) : unit
  requires len flux = len down && len flux2 = len down && w >= 3 && w < max usize && c < len down
  requires forall (j in 0 .. len down). j = c || flux2.[j] = flux.[j]
  ensures forall (k in 0 .. len down). (k = c || down.[c] <> k) ==> from down flux2 w k d = from down flux w k d
  with from
= ()
```

The same, two directions at a time.

```pia
let lemma frame_pair (down : [usize]) (flux : [u32]) (flux2 : [u32]) (w : usize) (c : usize) (h : int{0..3}) : unit
  requires len flux = len down && len flux2 = len down && w >= 3 && w < max usize && c < len down
  requires forall (j in 0 .. len down). j = c || flux2.[j] = flux.[j]
  ensures forall (k in 0 .. len down). (k = c || down.[c] <> k) ==> pair down flux2 w k h = pair down flux w k h
= if h = 0 then (frame_dir down flux flux2 w c 0; frame_dir down flux flux2 w c 1)
  else if h = 1 then (frame_dir down flux flux2 w c 2; frame_dir down flux flux2 w c 3)
  else if h = 2 then (frame_dir down flux flux2 w c 4; frame_dir down flux flux2 w c 5)
  else (frame_dir down flux flux2 w c 6; frame_dir down flux flux2 w c 7)
```

Four at a time.

```pia
let lemma frame_half (down : [usize]) (flux : [u32]) (flux2 : [u32]) (w : usize) (c : usize) (g : int{0..1}) : unit
  requires len flux = len down && len flux2 = len down && w >= 3 && w < max usize && c < len down
  requires forall (j in 0 .. len down). j = c || flux2.[j] = flux.[j]
  ensures forall (k in 0 .. len down). (k = c || down.[c] <> k) ==> half down flux2 w k g = half down flux w k g
= if g = 0 then (frame_pair down flux flux2 w c 0; frame_pair down flux flux2 w c 1)
  else (frame_pair down flux flux2 w c 2; frame_pair down flux flux2 w c 3)
```

```pia
let lemma frame_all (down : [usize]) (flux : [u32]) (flux2 : [u32]) (w : usize) (c : usize) : unit
  requires len flux = len down && len flux2 = len down && w >= 3 && w < max usize && c < len down
  requires forall (j in 0 .. len down). j = c || flux2.[j] = flux.[j]
  ensures forall (k in 0 .. len down). (k = c || down.[c] <> k) ==> inflow_of down flux2 w k = inflow_of down flux w k
  with inflow_of
= frame_half down flux flux2 w c 0; frame_half down flux flux2 w c 1
```

Every cell processed before position `p` took exactly its upstream neighbours' loads.

```pia
let spec linked_upto (down : [usize]) (flux : [u32]) (seen : [u64]) (pos : [usize]) (p : usize) (w : usize) : bool @opaque
  requires len flux = len down && len seen = len down && len pos = len down && w >= 3 && w < max usize
= forall (k in 0 .. len down). at pos k < p ==> seen.[k] = inflow_of down flux w k
```

Processing c changes flux and seen at c only. The cells done before c are not below c, so their inflow does not read flux at c.

```pia
let lemma linked_step (down : [usize]) (flux : [u32]) (seen : [u64]) (flux2 : [u32]) (seen2 : [u64])
    (pos : [usize]) (p : usize) (w : usize) (c : usize) : unit
  requires len flux = len down && len seen = len down && len pos = len down
  requires len flux2 = len down && len seen2 = len down && w >= 3 && w < max usize
  requires c < len down && pos.[c] = p
  requires forall (k in 0 .. len down). k = c || (flux2.[k] = flux.[k] && seen2.[k] = seen.[k])
  requires forall (k in 0 .. len down). at pos k < p ==> down.[c] <> k
  requires forall (k in 0 .. len down). at pos k = p ==> k = c
  requires linked_upto down flux seen pos p w
  requires seen2.[c] = inflow_of down flux2 w c
  ensures linked_upto down flux2 seen2 pos (p + 1) w
  with linked_upto
= frame_all down flux flux2 w c
```

Away from the cell c drains into, processing c leaves every partial inflow as it was.

```pia
let lemma pstep_dir (down : [usize]) (flux : [u32]) (flux2 : [u32]) (pos : [usize]) (p : usize) (w : usize) (c : usize) (d : int{0..7}) : unit
  requires len flux = len down && len flux2 = len down && len pos = len down && c < len down && pos.[c] = p && p < len down
  requires forall (j in 0 .. len down). j = c || flux2.[j] = flux.[j]
  requires forall (j in 0 .. len down). at pos j = p ==> j = c
  ensures forall (k in 0 .. len down). (k <> c && down.[c] <> k) ==> pterm down flux2 pos (p + 1) w k d = pterm down flux pos p w k d
  with pterm
= ()
```

The same, two directions at a time.

```pia
let lemma pstep_pair (down : [usize]) (flux : [u32]) (flux2 : [u32]) (pos : [usize]) (p : usize) (w : usize) (c : usize) (h : int{0..3}) : unit
  requires len flux = len down && len flux2 = len down && len pos = len down && c < len down && pos.[c] = p && p < len down
  requires forall (j in 0 .. len down). j = c || flux2.[j] = flux.[j]
  requires forall (j in 0 .. len down). at pos j = p ==> j = c
  ensures forall (k in 0 .. len down). (k <> c && down.[c] <> k) ==> ppair down flux2 pos (p + 1) w k h = ppair down flux pos p w k h
= if h = 0 then (pstep_dir down flux flux2 pos p w c 0; pstep_dir down flux flux2 pos p w c 1)
  else if h = 1 then (pstep_dir down flux flux2 pos p w c 2; pstep_dir down flux flux2 pos p w c 3)
  else if h = 2 then (pstep_dir down flux flux2 pos p w c 4; pstep_dir down flux flux2 pos p w c 5)
  else (pstep_dir down flux flux2 pos p w c 6; pstep_dir down flux flux2 pos p w c 7)
```

Four at a time.

```pia
let lemma pstep_half (down : [usize]) (flux : [u32]) (flux2 : [u32]) (pos : [usize]) (p : usize) (w : usize) (c : usize) (g : int{0..1}) : unit
  requires len flux = len down && len flux2 = len down && len pos = len down && c < len down && pos.[c] = p && p < len down
  requires forall (j in 0 .. len down). j = c || flux2.[j] = flux.[j]
  requires forall (j in 0 .. len down). at pos j = p ==> j = c
  ensures forall (k in 0 .. len down). (k <> c && down.[c] <> k) ==> phalf down flux2 pos (p + 1) w k g = phalf down flux pos p w k g
= if g = 0 then (pstep_pair down flux flux2 pos p w c 0; pstep_pair down flux flux2 pos p w c 1)
  else (pstep_pair down flux flux2 pos p w c 2; pstep_pair down flux flux2 pos p w c 3)
```

All eight.

```pia
let lemma pstep_all (down : [usize]) (flux : [u32]) (flux2 : [u32]) (pos : [usize]) (p : usize) (w : usize) (c : usize) : unit
  requires len flux = len down && len flux2 = len down && len pos = len down && c < len down && pos.[c] = p && p < len down
  requires forall (j in 0 .. len down). j = c || flux2.[j] = flux.[j]
  requires forall (j in 0 .. len down). at pos j = p ==> j = c
  ensures forall (k in 0 .. len down). (k <> c && down.[c] <> k) ==> pinflow down flux2 pos (p + 1) w k = pinflow down flux pos p w k
= pstep_half down flux flux2 pos p w c 0; pstep_half down flux flux2 pos p w c 1
```

At the cell c drains into, the term for the direction that names c gains c's load.

```pia
let lemma hit_dir (down : [usize]) (flux : [u32]) (flux2 : [u32]) (pos : [usize]) (p : usize) (w : usize) (c : usize) (d : int{0..7}) : unit
  requires len flux = len down && len flux2 = len down && len pos = len down && c < len down && pos.[c] = p && p < len down
  requires forall (j in 0 .. len down). j = c || flux2.[j] = flux.[j]
  requires forall (j in 0 .. len down). at pos j = p ==> j = c
  requires down.[c] < len down && down.[c] <> c
  ensures pterm down flux2 pos (p + 1) w (down.[c]) d =
    pterm down flux pos p w (down.[c]) d + (if nbr (len down) w (down.[c]) d = c then flux2.[c] else 0)
  with pterm
= ()
```

`x` if direction `d` of `k` names `c`, else 0.

```pia
let spec named (n : usize) (w : usize) (k : usize) (c : usize) (x : u32) (d : int{0..7}) : u64
  ensures result <= max u32
= if nbr n w k d = c then x else 0
```

A neighbour is named by exactly one of the eight directions.

```pia
let lemma named_once (n : usize) (w : usize) (k : usize) (c : usize) (x : u32) : unit
  requires w >= 3 && w < max usize && k < n && c < n && k <> c && adjacent w c k
  ensures (named n w k c x 0 + named n w k c x 1) + (named n w k c x 2 + named n w k c x 3)
    + ((named n w k c x 4 + named n w k c x 5) + (named n w k c x 6 + named n w k c x 7)) = x
= ()
```

(x0 + a) + (x1 + b) = (x0 + x1) + (a + b), on its own, away from the quantifiers.

```pia
let lemma regroup (x0 : u64) (x1 : u64) (y0 : u64) (y1 : u64) (a : u64) (b : u64) (y : u64) (x : u64) : unit
  requires x0 <= 17'179'869'180 && x1 <= 17'179'869'180 && a <= 17'179'869'180 && b <= 17'179'869'180
  requires y0 = x0 + a && y1 = x1 + b && y = y0 + y1 && x = x0 + x1
  ensures y = x + (a + b)
= ()
```

```pia
let lemma pstep_hit (down : [usize]) (flux : [u32]) (flux2 : [u32]) (pos : [usize]) (p : usize) (w : usize) (c : usize) : unit
  requires len flux = len down && len flux2 = len down && len pos = len down && c < len down && pos.[c] = p && p < len down
  requires w >= 3 && w < max usize
  requires forall (j in 0 .. len down). j = c || flux2.[j] = flux.[j]
  requires forall (j in 0 .. len down). at pos j = p ==> j = c
  requires down.[c] < len down && down.[c] <> c && adjacent w c (down.[c])
  ensures pinflow down flux2 pos (p + 1) w (down.[c]) = pinflow down flux pos p w (down.[c]) + flux2.[c]
= let k = down.[c] in
  hit_dir down flux flux2 pos p w c 0; hit_dir down flux flux2 pos p w c 1;
  hit_dir down flux flux2 pos p w c 2; hit_dir down flux flux2 pos p w c 3;
  hit_dir down flux flux2 pos p w c 4; hit_dir down flux flux2 pos p w c 5;
  hit_dir down flux flux2 pos p w c 6; hit_dir down flux flux2 pos p w c 7;
  named_once (len down) w k c (flux2.[c]);
  let x = flux2.[c] in
  let n = len down in
  assert ppair down flux2 pos (p + 1) w k 0 = ppair down flux pos p w k 0 + (named n w k c x 0 + named n w k c x 1);
  assert ppair down flux2 pos (p + 1) w k 1 = ppair down flux pos p w k 1 + (named n w k c x 2 + named n w k c x 3);
  assert ppair down flux2 pos (p + 1) w k 2 = ppair down flux pos p w k 2 + (named n w k c x 4 + named n w k c x 5);
  assert ppair down flux2 pos (p + 1) w k 3 = ppair down flux pos p w k 3 + (named n w k c x 6 + named n w k c x 7);
  assert phalf down flux2 pos (p + 1) w k 0 = phalf down flux pos p w k 0
    + ((named n w k c x 0 + named n w k c x 1) + (named n w k c x 2 + named n w k c x 3));
  assert phalf down flux2 pos (p + 1) w k 1 = phalf down flux pos p w k 1
    + ((named n w k c x 4 + named n w k c x 5) + (named n w k c x 6 + named n w k c x 7));
  let ab = ((named n w k c x 0 + named n w k c x 1) + (named n w k c x 2 + named n w k c x 3))
    + ((named n w k c x 4 + named n w k c x 5) + (named n w k c x 6 + named n w k c x 7)) in
  assert ab = x;
  let a0 = (named n w k c x 0 + named n w k c x 1) + (named n w k c x 2 + named n w k c x 3) in
  let b0 = (named n w k c x 4 + named n w k c x 5) + (named n w k c x 6 + named n w k c x 7) in
  regroup (phalf down flux pos p w k 0) (phalf down flux pos p w k 1)
    (phalf down flux2 pos (p + 1) w k 0) (phalf down flux2 pos (p + 1) w k 1) a0 b0
    (pinflow down flux2 pos (p + 1) w k) (pinflow down flux pos p w k)
```

Every cell not processed yet has received exactly the loads of its processed upstream neighbours.

```pia
let spec pending (down : [usize]) (flux : [u32]) (pos : [usize]) (inflow : [u32]) (bed : [u32]) (bed0 : [u32]) (p : usize) (w : usize) : bool @opaque
  requires len flux = len down && len pos = len down && len inflow = len down && len bed = len down && len bed0 = len down
  requires w >= 3 && w < max usize
= forall (k in 0 .. len down). at pos k >= p ==> inflow.[k] = pinflow down flux pos p w k && bed.[k] = bed0.[k]
```

```pia
let lemma pending_step (down : [usize]) (flux : [u32]) (flux2 : [u32]) (pos : [usize])
    (inflow : [u32]) (inflow2 : [u32]) (bed : [u32]) (bed2 : [u32]) (bed0 : [u32]) (p : usize) (w : usize) (c : usize) : unit
  requires len flux = len down && len flux2 = len down && len pos = len down
  requires len inflow = len down && len inflow2 = len down && len bed = len down && len bed2 = len down && len bed0 = len down
  requires w >= 3 && w < max usize && c < len down && pos.[c] = p && p < len down
  requires forall (j in 0 .. len down). j = c || flux2.[j] = flux.[j]
  requires forall (j in 0 .. len down). j = c || bed2.[j] = bed.[j]
  requires forall (j in 0 .. len down). j = c || j = down.[c] || inflow2.[j] = inflow.[j]
  requires forall (j in 0 .. len down). at pos j = p ==> j = c
  requires down.[c] < len down
  requires down.[c] = c || (adjacent w c (down.[c]) && inflow2.[down.[c]] = inflow.[down.[c]] + flux2.[c])
  requires pending down flux pos inflow bed bed0 p w
  ensures pending down flux2 pos inflow2 bed2 bed0 (p + 1) w
  with pending
= pstep_all down flux flux2 pos p w c;
  if down.[c] <> c then pstep_hit down flux flux2 pos p w c else ()
```

Every processed cell has settled, and has no inflow left.

```pia
let spec done_upto (fill : [u16]) (down : [usize]) (acc : [u32]) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64])
    (inflow : [u32]) (pos : [usize]) (p : usize) : bool @opaque
  requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill
  requires len seen = len fill && len inflow = len fill && len pos = len fill
  requires forall (k in 0 .. len down). down.[k] < len fill
= forall (k in 0 .. len fill). at pos k < p ==> holds fill down acc bed0 bed flux seen k && inflow.[k] = 0
```

```pia
let lemma done_step (fill : [u16]) (down : [usize]) (acc : [u32]) (bed0 : [u32])
    (bed : [u32]) (flux : [u32]) (seen : [u64]) (inflow : [u32])
    (bed2 : [u32]) (flux2 : [u32]) (seen2 : [u64]) (inflow2 : [u32]) (pos : [usize]) (p : usize) (c : usize) : unit
  requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill
  requires len seen = len fill && len inflow = len fill && len pos = len fill
  requires len bed2 = len fill && len flux2 = len fill && len seen2 = len fill && len inflow2 = len fill
  requires forall (k in 0 .. len down). down.[k] < len fill
  requires c < len fill && pos.[c] = p
  requires forall (j in 0 .. len fill). j = c || (bed2.[j] = bed.[j] && flux2.[j] = flux.[j] && seen2.[j] = seen.[j])
  requires forall (j in 0 .. len fill). j = c || j = down.[c] || inflow2.[j] = inflow.[j]
  requires forall (j in 0 .. len fill). at pos j < p ==> j <> down.[c]
  requires forall (j in 0 .. len fill). at pos j = p ==> j = c
  requires holds fill down acc bed0 bed2 flux2 seen2 c && inflow2.[c] = 0
  requires done_upto fill down acc bed0 bed flux seen inflow pos p
  ensures done_upto fill down acc bed0 bed2 flux2 seen2 inflow2 pos (p + 1)
  with done_upto
= ()
```

## 3. The sequential step, recording what each cell took

From here to `visit`, the pieces of [sediment.pia.md](sediment.pia.md) sections 1 to 3, copied because a module cannot export lemmas over buffers yet ([#327](https://github.com/deanberris/pia-lang/issues/327)), with stronger postconditions: the exact bed and load each function leaves, and what it leaves alone. An element of a sum, with its `u32` range.

```pia
let spec elt (xs : [u32]) (i : usize) : u32
  requires i < len xs
= xs.[i]
```

The sum of a prefix.

```pia
let spec sum (xs : [u32]) (n : usize) : u64
  requires n <= len xs && n <= max u32 + 1
  ensures result <= (max u32 + 1) * n
  decreases n
= if n = 0 then 0 else sum xs (n - 1) + elt xs (n - 1)
```

```pia
let lemma step (xs : [u32]) (ys : [u32]) (n : usize) : unit
  requires 0 < n && n <= len xs && n <= len ys && n <= max u32 + 1
  requires sum ys (n - 1) = sum xs (n - 1) && ys.[n - 1] = xs.[n - 1]
  ensures sum ys n = sum xs n
= ()
```

```pia
let lemma step_after (xs : [u32]) (ys : [u32]) (i : usize) (n : usize) : unit
  requires i < n - 1 && n <= len xs && n <= len ys && n <= max u32 + 1
  requires sum ys (n - 1) + xs.[i] = sum xs (n - 1) + ys.[i] && ys.[n - 1] = xs.[n - 1]
  ensures sum ys n + xs.[i] = sum xs n + ys.[i]
= ()
```

```pia
let lemma step_at (xs : [u32]) (ys : [u32]) (i : usize) : unit
  requires i < len xs && i < len ys && i < max u32 + 1
  requires sum ys i = sum xs i
  ensures sum ys (i + 1) + xs.[i] = sum xs (i + 1) + ys.[i]
= ()
```

```pia
let lemma frame (xs : [u32]) (ys : [u32]) (i : usize) (n : usize) : unit
  requires len xs = len ys && n <= i && i < len xs && len xs <= max u32 + 1
  requires forall (k in 0 .. len xs). k <> i ==> ys.[k] = xs.[k]
  ensures sum ys n = sum xs n
  decreases n
= if n > 0 then (frame xs ys i (n - 1); assert ys.[n - 1] = xs.[n - 1]; step xs ys n)
```

```pia
let lemma update (xs : [u32]) (ys : [u32]) (i : usize) (n : usize) : unit
  requires len xs = len ys && i < n && n <= len xs && len xs <= max u32 + 1
  requires forall (k in 0 .. len xs). k <> i ==> ys.[k] = xs.[k]
  ensures sum ys n + xs.[i] = sum xs n + ys.[i]
  decreases n
= if n > i + 1 then (update xs ys i (n - 1); assert ys.[n - 1] = xs.[n - 1]; step_after xs ys i n)
  else (frame xs ys i i; step_at xs ys i; assert n = i + 1)
```

```pia
let lemma at_le (xs : [u32]) (i : usize) : unit
  requires i < len xs && i < max u32 + 1
  ensures xs.[i] <= sum xs (i + 1)
= ()
```

```pia
let lemma mono (xs : [u32]) (m : usize) (n : usize) : unit
  requires m <= n && n <= len xs && n <= max u32 + 1
  ensures sum xs m <= sum xs n
  decreases n
= if n > m then mono xs m (n - 1)
```

```pia
let lemma elt_le (xs : [u32]) (i : usize) (n : usize) : unit
  requires i < n && n <= len xs && n <= max u32 + 1
  ensures xs.[i] <= sum xs n
= at_le xs i; mono xs (i + 1) n
```

```pia
let lemma zero (xs : [u32]) (n : usize) : unit
  requires n <= len xs && n <= max u32 + 1
  requires forall (k in 0 .. n). xs.[k] = 0
  ensures sum xs n = 0
  decreases n
= if n > 0 then (zero xs (n - 1); assert xs.[n - 1] = 0)
```

A point update, with the sum's change.

```pia
let set (xs : borrowed inout mutable [u32]) (i : usize) (v : u32) : unit
  requires i < len xs && len xs <= max u32 + 1
  ensures xs.[i] = v
  ensures forall (k in 0 .. len xs). k <> i ==> xs.[k] = old (xs.[k])
  ensures sum xs (len xs) + old (xs.[i]) = sum (old xs) (len xs) + v
= let w = xs.[i] in
  xs.[i] <- v;
  update (old xs) xs i (len xs);
  assert w = old (xs.[i])
```

```pia
let cell = type { bed : u32; load : u32 }
```

Erosion or deposition at one cell; it now also says its result is `eb` and `el`.

```pia
let erode_or_deposit (inflow : u32) (capacity : u32) (bed : u32) : cell
  requires bed + inflow <= max u32
  ensures result.bed + result.load = bed + inflow
  ensures inflow < capacity ==> result.bed <= bed && inflow <= result.load && result.load <= capacity
  ensures capacity <= inflow ==> bed <= result.bed && result.load = capacity
  ensures result.bed = eb inflow capacity bed && result.load = el inflow capacity bed
= if inflow < capacity then
    (let room = capacity - inflow in
     let e = if room < bed then room else bed in
     { bed = bed - e; load = inflow + e })
  else { bed = bed + (inflow - capacity); load = capacity }
```

Moves cell `a`'s load into cell `b`'s inflow.

```pia
let push (load : borrowed inout mutable [u32]) (inflow : borrowed inout mutable [u32]) (a : usize) (b : usize) : unit
  requires a < len load && b < len inflow && len load <= max u32 + 1 && len inflow <= max u32 + 1
  requires sum load (len load) + sum inflow (len inflow) <= max u32
  ensures load.[a] = 0
  ensures forall (k in 0 .. len load). k <> a ==> load.[k] = old (load.[k])
  ensures sum load (len load) + sum inflow (len inflow) = sum (old load) (len load) + sum (old inflow) (len inflow)
  ensures inflow.[b] = old (inflow.[b]) + old (load.[a])
  ensures forall (k in 0 .. len inflow). k <> b ==> inflow.[k] = old (inflow.[k])
= let m = load.[a] in
  let w = inflow.[b] in
  elt_le load a (len load);
  elt_le inflow b (len inflow);
  set load a 0;
  set inflow b (w + m)
```

An outlet's load leaves the map.

```pia
let drain (load : borrowed inout mutable [u32]) (a : usize) (gone : u64) : u64
  requires a < len load && len load <= max u32 + 1
  requires sum load (len load) + gone <= max u32
  ensures load.[a] = 0
  ensures forall (k in 0 .. len load). k <> a ==> load.[k] = old (load.[k])
  ensures sum load (len load) + result = sum (old load) (len load) + gone
  ensures result = gone + old (load.[a])
= let m = load.[a] in
  elt_le load a (len load);
  set load a 0;
  gone + m
```

The arithmetic of `erode_cell`'s three writes.

```pia
let lemma balance (a : u64) (b : u64) (c : u64) (a0 : u64) (b0 : u64) (c0 : u64) (d : u32) (i : u32) (rb : u32) (rl : u32) : unit
  requires a + d = a0 + rb && b = b0 + rl && c + i = c0 && rb + rl = d + i
  ensures a + b + c = a0 + b0 + c0
= ()
```

One cell erodes or deposits.

```pia
let erode_cell (bed : borrowed inout mutable [u32]) (load : borrowed inout mutable [u32]) (inflow : borrowed inout mutable [u32]) (c : usize) (capacity : u32) : unit
  requires c < len bed && c < len load && c < len inflow
  requires len bed <= max u32 + 1 && len load <= max u32 + 1 && len inflow <= max u32 + 1
  requires sum bed (len bed) + sum inflow (len inflow) <= max u32
  requires load.[c] = 0
  ensures inflow.[c] = 0
  ensures forall (k in 0 .. len load). k <> c ==> load.[k] = old (load.[k])
  ensures sum bed (len bed) + sum load (len load) + sum inflow (len inflow) =
    sum (old bed) (len bed) + sum (old load) (len load) + sum (old inflow) (len inflow)
  ensures old (inflow.[c]) + old (bed.[c]) <= max u32
    && bed.[c] = eb (old (inflow.[c])) capacity (old (bed.[c])) && load.[c] = el (old (inflow.[c])) capacity (old (bed.[c]))
  ensures forall (k in 0 .. len bed). k <> c ==> bed.[k] = old (bed.[k])
  ensures forall (k in 0 .. len inflow). k <> c ==> inflow.[k] = old (inflow.[k])
= let i = inflow.[c] in
  let d = bed.[c] in
  elt_le bed c (len bed);
  elt_le inflow c (len inflow);
  let r = erode_or_deposit i capacity d in
  set bed c r.bed;
  assert sum bed (len bed) + d = sum (old bed) (len bed) + r.bed;
  set load c r.load;
  assert sum load (len load) = sum (old load) (len load) + r.load;
  set inflow c 0;
  assert sum inflow (len inflow) + i = sum (old inflow) (len inflow);
  balance (sum bed (len bed)) (sum load (len load)) (sum inflow (len inflow))
    (sum (old bed) (len bed)) (sum (old load) (len load)) (sum (old inflow) (len inflow))
    d i r.bed r.load
```

Its load moves on, or off the map.

```pia
let transfer (bed : [u32]) (load : borrowed inout mutable [u32]) (inflow : borrowed inout mutable [u32]) (a : usize) (b : usize) (outlet : bool) (gone : u64) : u64
  requires a < len load && b < len inflow
  requires len bed <= max u32 + 1 && len load <= max u32 + 1 && len inflow <= max u32 + 1
  requires sum bed (len bed) + sum load (len load) + sum inflow (len inflow) + gone <= max u32
  ensures load.[a] = 0
  ensures forall (k in 0 .. len load). k <> a ==> load.[k] = old (load.[k])
  ensures sum bed (len bed) + sum load (len load) + sum inflow (len inflow) + result =
    sum bed (len bed) + sum (old load) (len load) + sum (old inflow) (len inflow) + gone
  ensures outlet ==> (forall (k in 0 .. len inflow). inflow.[k] = old (inflow.[k]))
  ensures outlet ==> result = gone + old (load.[a])
  ensures outlet = false ==> result = gone
  ensures outlet = false ==> inflow.[b] = old (inflow.[b]) + old (load.[a])
  ensures outlet = false ==> (forall (k in 0 .. len inflow). k <> b ==> inflow.[k] = old (inflow.[k]))
= if outlet then drain load a gone
  else (push load inflow a b; gone)
```

The bound before `transfer`.

```pia
let lemma chain (b : u64) (l : u64) (i : u64) (g : u64) (b1 : u64) (l1 : u64) (i1 : u64) : unit
  requires b + l + i + g <= max u32 && b1 + l1 + i1 = b + l + i
  ensures b1 + l1 + i1 + g <= max u32
= ()
```

The capacity of the water leaving a cell.

```pia
let capacity_of (a : u32) (drop : u16) : u32
  ensures result = cap_rule a drop
=
  let d : u32 = drop in
  let c : u64 = (a >> 4) + (d << 2) in
  if c < max u16 then c else max u16
```

One cell of the sequential step, with every value it leaves.

```pia
let visit (bed : borrowed inout mutable [u32]) (load : borrowed inout mutable [u32]) (inflow : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32]) (c : usize) (d : usize) (capacity : u32) (gone : u64) : u64
  requires c < len bed && c < len load && c < len inflow && d < len inflow && c < len flux
  requires len bed <= max u32 + 1 && len load <= max u32 + 1 && len inflow <= max u32 + 1
  requires load.[c] = 0
  requires sum bed (len bed) + sum load (len load) + sum inflow (len inflow) + gone <= max u32
  ensures load.[c] = 0
  ensures forall (k in 0 .. len load). k <> c ==> load.[k] = old (load.[k])
  ensures sum bed (len bed) + sum load (len load) + sum inflow (len inflow) + result =
    sum (old bed) (len bed) + sum (old load) (len load) + sum (old inflow) (len inflow) + gone
  ensures old (inflow.[c]) + old (bed.[c]) <= max u32
    && bed.[c] = eb (old (inflow.[c])) capacity (old (bed.[c])) && flux.[c] = el (old (inflow.[c])) capacity (old (bed.[c]))
  ensures forall (k in 0 .. len bed). k <> c ==> bed.[k] = old (bed.[k])
  ensures forall (k in 0 .. len flux). k <> c ==> flux.[k] = old (flux.[k])
  ensures inflow.[c] = 0
  ensures d <> c ==> inflow.[d] = old (inflow.[d]) + flux.[c]
  ensures forall (k in 0 .. len inflow). (k <> c && k <> d) ==> inflow.[k] = old (inflow.[k])
  ensures d = c ==> result = gone + flux.[c]
  ensures d <> c ==> result = gone
= erode_cell bed load inflow c capacity;
  chain (sum (old bed) (len bed)) (sum (old load) (len load)) (sum (old inflow) (len inflow)) gone
    (sum bed (len bed)) (sum load (len load)) (sum inflow (len inflow));
  flux.[c] <- load.[c];
  let r = transfer bed load inflow c d (d = c) gone in
  r
```

At the start nothing is processed, so every partial inflow is 0.

```pia
let lemma pzero_dir (down : [usize]) (flux : [u32]) (pos : [usize]) (w : usize) (d : int{0..7}) : unit
  ensures forall (k in 0 .. len down). pterm down flux pos 0 w k d = 0
  with pterm
= ()
```

```pia
let lemma pzero_pair (down : [usize]) (flux : [u32]) (pos : [usize]) (w : usize) (h : int{0..3}) : unit
  ensures forall (k in 0 .. len down). ppair down flux pos 0 w k h = 0
= if h = 0 then (pzero_dir down flux pos w 0; pzero_dir down flux pos w 1)
  else if h = 1 then (pzero_dir down flux pos w 2; pzero_dir down flux pos w 3)
  else if h = 2 then (pzero_dir down flux pos w 4; pzero_dir down flux pos w 5)
  else (pzero_dir down flux pos w 6; pzero_dir down flux pos w 7)
```

```pia
let lemma pzero_half (down : [usize]) (flux : [u32]) (pos : [usize]) (w : usize) (g : int{0..1}) : unit
  ensures forall (k in 0 .. len down). phalf down flux pos 0 w k g = 0
= if g = 0 then (pzero_pair down flux pos w 0; pzero_pair down flux pos w 1)
  else (pzero_pair down flux pos w 2; pzero_pair down flux pos w 3)
```

The invariants of the sequential loop hold at the start.

```pia
let lemma start_seq (fill : [u16]) (down : [usize]) (acc : [u32]) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64])
    (inflow : [u32]) (pos : [usize]) (w : usize) : unit
  requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill
  requires len seen = len fill && len inflow = len fill && len pos = len fill && w >= 3 && w < max usize
  requires forall (k in 0 .. len down). down.[k] < len fill
  requires forall (k in 0 .. len fill). inflow.[k] = 0 && bed.[k] = bed0.[k]
  ensures pending down flux pos inflow bed bed0 0 w
  ensures done_upto fill down acc bed0 bed flux seen inflow pos 0
  ensures linked_upto down flux seen pos 0 w
  with pending, done_upto, linked_upto
= pzero_half down flux pos w 0; pzero_half down flux pos w 1
```

`pending`, at one cell.

```pia
let lemma use_pending (down : [usize]) (flux : [u32]) (pos : [usize]) (inflow : [u32]) (bed : [u32]) (bed0 : [u32]) (p : usize) (w : usize) (c : usize) : unit
  requires len flux = len down && len pos = len down && len inflow = len down && len bed = len down && len bed0 = len down
  requires w >= 3 && w < max usize && c < len down && pos.[c] >= p
  requires pending down flux pos inflow bed bed0 p w
  ensures inflow.[c] = pinflow down flux pos p w c && bed.[c] = bed0.[c]
  with pending
= ()
```

Every cell has settled.

```pia
let spec settled (fill : [u16]) (down : [usize]) (acc : [u32]) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) : bool @opaque
  requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill && len seen = len fill
  requires forall (k in 0 .. len down). down.[k] < len fill
= forall (k in 0 .. len fill). holds fill down acc bed0 bed flux seen k
```

Every cell took exactly its upstream neighbours' loads.

```pia
let spec linked (down : [usize]) (flux : [u32]) (seen : [u64]) (w : usize) : bool @opaque
  requires len flux = len down && len seen = len down && w >= 3 && w < max usize
= forall (k in 0 .. len down). seen.[k] = inflow_of down flux w k
```

At the end of the loop every cell is processed.

```pia
let lemma finish_seq (fill : [u16]) (down : [usize]) (acc : [u32]) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64])
    (inflow : [u32]) (pos : [usize]) (w : usize) : unit
  requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill
  requires len seen = len fill && len inflow = len fill && len pos = len fill && w >= 3 && w < max usize
  requires forall (k in 0 .. len down). down.[k] < len fill
  requires forall (k in 0 .. len pos). pos.[k] < len fill
  requires done_upto fill down acc bed0 bed flux seen inflow pos (len fill)
  requires linked_upto down flux seen pos (len fill) w
  ensures settled fill down acc bed0 bed flux seen
  ensures linked down flux seen w
  ensures forall (k in 0 .. len fill). inflow.[k] = 0
  with done_upto, linked_upto, settled, linked
= ()
```

What the outlets among the first p cells of the order sent off the map.

```pia
let spec oterm (order : [usize]) (down : [usize]) (flux : [u32]) (q : usize) : u32
= if q < len order then
    (let c = order.[q] in if c < len down && c < len flux then (if down.[c] = c then flux.[c] else 0) else 0)
  else 0
```

What the outlets among the first `p` cells sent off the map.

```pia
let spec osum (order : [usize]) (down : [usize]) (flux : [u32]) (p : usize) : u64 @opaque
  requires p <= max u32 + 1
  ensures result <= (max u32 + 1) * p
  decreases p
= if p = 0 then 0 else osum order down flux (p - 1) + oterm order down flux (p - 1)
```

One more cell.

```pia
let lemma osum_next (order : [usize]) (down : [usize]) (flux : [u32]) (p : usize) : unit
  requires p < max u32 + 1
  ensures osum order down flux (p + 1) = osum order down flux p + oterm order down flux p
  with osum
= ()
```

g is the gone of the first p cells: what came in, and what their outlets sent off.

```pia
let spec gone_ok (order : [usize]) (down : [usize]) (flux : [u32]) (g : u64) (gone : u64) (p : usize) : bool @opaque
  requires p <= max u32 + 1
= if osum order down flux p > max u64 - gone then false else g = gone + osum order down flux p
```

Changing flux at a cell after the first p in the order leaves their sum alone.

```pia
let lemma osum_frame (order : [usize]) (down : [usize]) (flux : [u32]) (flux2 : [u32]) (c : usize) (p : usize) : unit
  requires len flux2 = len flux && p <= len order && p <= max u32 + 1
  requires forall (j in 0 .. len flux). j = c || flux2.[j] = flux.[j]
  requires forall (q in 0 .. p). order.[q] <> c
  ensures osum order down flux2 p = osum order down flux p
  decreases p
  with osum
= if p > 0 then (
    osum_frame order down flux flux2 c (p - 1);
    assert order.[p - 1] <> c;
    assert oterm order down flux2 (p - 1) = oterm order down flux (p - 1)
  ) else ()
```

The same loads send off the same mass.

```pia
let lemma osum_eq (order : [usize]) (down : [usize]) (fa : [u32]) (fb : [u32]) (p : usize) : unit
  requires len fb = len fa && p <= len order && p <= max u32 + 1
  requires forall (j in 0 .. len fa). fa.[j] = fb.[j]
  ensures osum order down fa p = osum order down fb p
  decreases p
  with osum
= if p > 0 then (
    osum_eq order down fa fb (p - 1);
    let c = order.[p - 1] in
    (if c < len fa then assert fa.[c] = fb.[c] else ());
    assert oterm order down fa (p - 1) = oterm order down fb (p - 1)
  ) else ()
```

The arithmetic of one cell's share of `gone`.

```pia
let lemma add_sent (g : u64) (gone : u64) (x : u32) (outlet : bool) (t : u32) : unit
  requires outlet ==> g = gone + x
  requires outlet = false ==> g = gone
  requires t = (if outlet then x else 0)
  ensures g = gone + t
= ()
```

`gone_ok`, unfolded.

```pia
let lemma gone_in (order : [usize]) (down : [usize]) (flux : [u32]) (g : u64) (gone : u64) (p : usize) : unit
  requires p <= max u32 + 1
  requires gone_ok order down flux g gone p
  ensures g = gone + osum order down flux p
  with gone_ok
= ()
```

`gone_ok`, one cell on.

```pia
let lemma gone_out (order : [usize]) (down : [usize]) (flux : [u32]) (g : u64) (gone : u64) (p : usize) : unit
  requires p < max u32 + 1
  requires g = gone + (osum order down flux p + oterm order down flux p)
  ensures gone_ok order down flux g gone (p + 1)
  with gone_ok
= osum_next order down flux p
```

`gone_ok` at the start.

```pia
let lemma gone_start (order : [usize]) (down : [usize]) (flux : [u32]) (gone : u64) : unit
  ensures gone_ok order down flux gone gone 0
  with gone_ok, osum
= ()
```

One cell of the sequential step, the cell at position p, keeping the three invariants and the conservation of transport.

```pia
let seq_cell (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (bed : borrowed inout mutable [u32]) (load : borrowed inout mutable [u32]) (inflow : borrowed inout mutable [u32])
    (flux : borrowed inout mutable [u32]) (seen : borrowed inout mutable [u64]) (p : usize) (gone : u64) (g0 : u64) : u64
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len bed = len fill && len load = len fill && len inflow = len fill && len flux = len fill && len seen = len fill
  requires len fill <= max u32 + 1 && p < len fill && w >= 3 && w < max usize
  requires forall (q in 0 .. len order). order.[q] < len pos && pos.[order.[q]] = q
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len down). down.[k] < len fill
  requires forall (k in 0 .. len down). down.[k] = k || adjacent w k (down.[k])
  requires forall (k in 0 .. len load). load.[k] = 0
  requires sum bed (len bed) + sum load (len load) + sum inflow (len inflow) + gone <= max u32
  requires done_upto fill down acc bed0 bed flux seen inflow pos p
  requires linked_upto down flux seen pos p w
  requires pending down flux pos inflow bed bed0 p w
  requires gone_ok order down flux gone g0 p
  ensures gone_ok order down flux result g0 (p + 1)
  ensures forall (k in 0 .. len load). load.[k] = 0
  ensures sum bed (len bed) + sum load (len load) + sum inflow (len inflow) + result =
    sum (old bed) (len bed) + sum (old load) (len load) + sum (old inflow) (len inflow) + gone
  ensures done_upto fill down acc bed0 bed flux seen inflow pos (p + 1)
  ensures linked_upto down flux seen pos (p + 1) w
  ensures pending down flux pos inflow bed bed0 (p + 1) w
=
  let c = order.[p] in
  let d = down.[c] in
  assert pos.[c] = p;
  assert (forall (j in 0 .. len fill). at pos j = p ==> j = c);
  if d <> c then later fill order pos c d else ();
  assert (forall (j in 0 .. len fill). at pos j < p ==> j <> d);
  use_pending down flux pos inflow bed bed0 p w c;
  all_in fill down order pos flux w c p;
  let i : u64 = inflow.[c] in
  seen.[c] <- i;
  let drop : u16 = if d = c then 0 else fill.[c] - fill.[d] in
  let g = visit bed load inflow flux c d (capacity_of acc.[c] drop) gone in
  assert holds fill down acc bed0 bed flux seen c;
  frame_all down (old flux) flux w c;
  linked_step down (old flux) (old seen) flux seen pos p w c;
  done_step fill down acc bed0 (old bed) (old flux) (old seen) (old inflow) bed flux seen inflow pos p c;
  pending_step down (old flux) flux pos (old inflow) inflow (old bed) bed bed0 p w c;
  assert (forall (r in 0 .. p). order.[r] <> c);
  osum_frame order down (old flux) flux c p;
  osum_next order down flux p;
  gone_in order down (old flux) gone g0 p;
  assert oterm order down flux p = (if d = c then flux.[c] else 0);
  add_sent g gone (flux.[c]) (d = c) (oterm order down flux p);
  gone_out order down flux g g0 p;
  g
```

The sequential step of docs/sediment.pia.md, highest cells first, with the inflow each cell took recorded in seen. Beyond transport's conservation, it is settled and linked from bed0, the bed it started from.

```pia
let transport_seen (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (bed : borrowed inout mutable [u32]) (load : borrowed inout mutable [u32]) (inflow : borrowed inout mutable [u32])
    (flux : borrowed inout mutable [u32]) (seen : borrowed inout mutable [u64]) (gone : u64) : u64
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len bed = len fill && len load = len fill && len inflow = len fill && len flux = len fill && len seen = len fill
  requires len fill <= max u32 + 1 && w >= 3 && w < max usize
  requires forall (q in 0 .. len order). order.[q] < len pos && pos.[order.[q]] = q
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len down). down.[k] < len fill
  requires forall (k in 0 .. len down). down.[k] = k || adjacent w k (down.[k])
  requires forall (k in 0 .. len fill). load.[k] = 0 && inflow.[k] = 0 && bed.[k] = bed0.[k]
  requires sum bed (len bed) + sum load (len load) + sum inflow (len inflow) + gone <= max u32
  ensures forall (k in 0 .. len load). load.[k] = 0
  ensures forall (k in 0 .. len inflow). inflow.[k] = 0
  ensures sum bed (len bed) + sum load (len load) + sum inflow (len inflow) + result =
    sum (old bed) (len bed) + sum (old load) (len load) + sum (old inflow) (len inflow) + gone
  ensures settled fill down acc bed0 bed flux seen
  ensures linked down flux seen w
  ensures result = gone + osum order down flux (len fill)
=
  start_seq fill down acc bed0 bed flux seen inflow pos w;
  gone_start order down flux gone;
  let g : mutable u64 = gone in
  for p in 0 .. len fill
    invariant forall (k in 0 .. len load). load.[k] = 0
    invariant sum bed (len bed) + sum load (len load) + sum inflow (len inflow) + g =
      sum (old bed) (len bed) + sum (old load) (len load) + sum (old inflow) (len inflow) + gone
    invariant done_upto fill down acc bed0 bed flux seen inflow pos p
    invariant linked_upto down flux seen pos p w
    invariant pending down flux pos inflow bed bed0 p w
    invariant gone_ok order down flux g gone p
  do
    g <- seq_cell fill down acc order pos w bed0 bed load inflow flux seen p g gone
  done;
  finish_seq fill down acc bed0 bed flux seen inflow pos w;
  gone_in order down flux g gone (len fill);
  g
```

```pia

```

## 4. The pull step

The neighbour `d` cells before `c`, or `n`.

```pia
let before (n : usize) (w : usize) (c : usize) (d : usize) : usize
  requires w >= 3 && w < max usize && c < n && (d = 1 || d = w - 1 || d = w || d = w + 1)
  ensures result = (if c >= d then c - d else n)
= if c >= d then c - d else n
```

The neighbour `d` cells after `c`, or `n`.

```pia
let after (n : usize) (w : usize) (c : usize) (d : usize) : usize
  requires w >= 3 && w < max usize && c < n && (d = 1 || d = w - 1 || d = w || d = w + 1)
  ensures result = (if d < n - c then c + d else n)
= if d < n - c then c + d else n
```

The neighbour in direction `d`: `nbr`, computed.

```pia
let neighbour (n : usize) (w : usize) (c : usize) (d : int{0..7}) : usize
  requires w >= 3 && w < max usize && c < n
  ensures result = nbr n w c d
=
  if d = 0 then before n w c (w + 1)
  else if d = 1 then before n w c w
  else if d = 2 then before n w c (w - 1)
  else if d = 3 then before n w c 1
  else if d = 4 then after n w c 1
  else if d = 5 then after n w c (w - 1)
  else if d = 6 then after n w c w
  else after n w c (w + 1)
```

The load neighbour d of c sends into c.

```pia
let pull_from (down : [usize]) (flux : [u32]) (w : usize) (c : usize) (d : int{0..7}) : u64
  requires len flux = len down && c < len down && w >= 3 && w < max usize
  ensures result = from down flux w c d
  with from
= let nb = neighbour (len down) w c d in
  if nb < len down then (if nb <> c && down.[nb] = c then flux.[nb] else 0) else 0
```

Everything c's upstream neighbours send it.

```pia
let gather (down : [usize]) (flux : [u32]) (w : usize) (c : usize) : u64
  requires len flux = len down && c < len down && w >= 3 && w < max usize
  ensures result = inflow_of down flux w c
  with inflow_of
= let a = pull_from down flux w c 0 + pull_from down flux w c 1 in
  let b = pull_from down flux w c 2 + pull_from down flux w c 3 in
  let e = pull_from down flux w c 4 + pull_from down flux w c 5 in
  let f = pull_from down flux w c 6 + pull_from down flux w c 7 in
  (a + b) + (e + f)
```

One wave, the cells at positions lo .. hi of the height order, as a spread: every cell pulls its inflow and erodes or deposits, writing only its own slots of gathered, newbed and newout.

```pia
let pull_wave (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (w : usize)
    (bed0 : [u32]) (flux : [u32]) (lo : usize) (hi : usize)
    (gathered : borrowed inout mutable [u64]) (newbed : borrowed inout mutable [u32])
    (newout : borrowed inout mutable [u32]) : unit
  requires len down = len fill && len acc = len fill && len order = len fill
  requires len bed0 = len fill && len flux = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill
  requires lo <= hi && hi <= len fill && w >= 3 && w < max usize
  requires forall (q in 0 .. len order). order.[q] < len fill
  requires forall (k in 0 .. len down). down.[k] < len fill
  requires forall (k in 0 .. len down). down.[k] = k || fill.[down.[k]] < fill.[k]
  ensures forall (q in lo .. hi). gathered.[q] = inflow_of down flux w (order.[q])
  ensures forall (q in lo .. hi). gathered.[q] + bed0.[order.[q]] <= max u32 ==>
    newbed.[q] = eb (gathered.[q]) (cap_of fill down acc (order.[q])) (bed0.[order.[q]])
    && newout.[q] = el (gathered.[q]) (cap_of fill down acc (order.[q])) (bed0.[order.[q]])
= spread q in lo .. hi
    ensures gathered.[q] = inflow_of down flux w (order.[q])
    ensures gathered.[q] + bed0.[order.[q]] <= max u32 ==>
      newbed.[q] = eb (gathered.[q]) (cap_of fill down acc (order.[q])) (bed0.[order.[q]])
      && newout.[q] = el (gathered.[q]) (cap_of fill down acc (order.[q])) (bed0.[order.[q]])
  do
    let c = order.[q] in
    let g = gather down flux w c in
    gathered.[q] <- g;
    let b = bed0.[c] in
    let d = down.[c] in
    let drop : u16 = if d = c then 0 else fill.[c] - fill.[d] in
    if g + b <= max u32 then (
      let r = erode_or_deposit g (capacity_of acc.[c] drop) b in
      newbed.[q] <- r.bed;
      newout.[q] <- r.load
    ) else (
      newbed.[q] <- b;
      newout.[q] <- 0
    )
  done
```

What the pull step promises for a cell: if its inflow and bed fit in a u32, its bed and load are what the sequential step gives.

```pia
let spec holds_if (fill : [u16]) (down : [usize]) (acc : [u32]) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) (c : usize) : bool
  requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill && len seen = len fill
  requires c < len fill
= if seen.[c] > max u32 then true
  else if seen.[c] + bed0.[c] > max u32 then true
  else bed.[c] = eb (seen.[c]) (cap_of fill down acc c) (bed0.[c])
       && flux.[c] = el (seen.[c]) (cap_of fill down acc c) (bed0.[c])
```

Every cell committed before position `p` keeps that promise.

```pia
let spec done_if_upto (fill : [u16]) (down : [usize]) (acc : [u32]) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64])
    (pos : [usize]) (p : usize) : bool @opaque
  requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill
  requires len seen = len fill && len pos = len fill
= forall (k in 0 .. len fill). at pos k < p ==> holds_if fill down acc bed0 bed flux seen k
```

The wave's slots from q on: their inflow still matches flux, and the kernel's results for them.

```pia
let spec ready_in (down : [usize]) (order : [usize]) (w : usize) (flux : [u32]) (gathered : [u64]) (q : usize) (hi : usize) : bool @opaque
  requires len order = len down && len flux = len down && len gathered = len down && hi <= len down
  requires forall (r in 0 .. len order). order.[r] < len down
  requires w >= 3 && w < max usize
= forall (r in q .. hi). gathered.[r] = inflow_of down flux w (at order r)
```

```pia
let spec ready_vals (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (bed0 : [u32])
    (gathered : [u64]) (newbed : [u32]) (newout : [u32]) (q : usize) (hi : usize) : bool @opaque
  requires len down = len fill && len acc = len fill && len order = len fill && len bed0 = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill && hi <= len fill
  requires forall (r in 0 .. len order). order.[r] < len fill
= forall (r in q .. hi). gathered.[r] + bed0.[order.[r]] <= max u32 ==>
    newbed.[r] = eb (gathered.[r]) (cap_of fill down acc (order.[r])) (bed0.[order.[r]])
    && newout.[r] = el (gathered.[r]) (cap_of fill down acc (order.[r])) (bed0.[order.[r]])
```

The kernel's postcondition, as the two invariants.

```pia
let lemma ready_init (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (w : usize) (bed0 : [u32]) (flux : [u32])
    (gathered : [u64]) (newbed : [u32]) (newout : [u32]) (lo : usize) (hi : usize) : unit
  requires len down = len fill && len acc = len fill && len order = len fill && len bed0 = len fill && len flux = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill && hi <= len fill
  requires forall (r in 0 .. len order). order.[r] < len fill
  requires w >= 3 && w < max usize
  requires forall (q in lo .. hi). gathered.[q] = inflow_of down flux w (order.[q])
  requires forall (q in lo .. hi). gathered.[q] + bed0.[order.[q]] <= max u32 ==>
    newbed.[q] = eb (gathered.[q]) (cap_of fill down acc (order.[q])) (bed0.[order.[q]])
    && newout.[q] = el (gathered.[q]) (cap_of fill down acc (order.[q])) (bed0.[order.[q]])
  ensures ready_in down order w flux gathered lo hi
  ensures ready_vals fill down acc order bed0 gathered newbed newout lo hi
  with ready_in, ready_vals
= ()
```

The invariants at the next slot.

```pia
let lemma use_ready (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (w : usize) (bed0 : [u32]) (flux : [u32])
    (gathered : [u64]) (newbed : [u32]) (newout : [u32]) (q : usize) (hi : usize) : unit
  requires len down = len fill && len acc = len fill && len order = len fill && len bed0 = len fill && len flux = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill && q < hi && hi <= len fill
  requires forall (r in 0 .. len order). order.[r] < len fill
  requires w >= 3 && w < max usize
  requires ready_in down order w flux gathered q hi
  requires ready_vals fill down acc order bed0 gathered newbed newout q hi
  ensures gathered.[q] = inflow_of down flux w (order.[q])
  ensures gathered.[q] + bed0.[order.[q]] <= max u32 ==>
    newbed.[q] = eb (gathered.[q]) (cap_of fill down acc (order.[q])) (bed0.[order.[q]])
    && newout.[q] = el (gathered.[q]) (cap_of fill down acc (order.[q])) (bed0.[order.[q]])
  ensures ready_vals fill down acc order bed0 gathered newbed newout (q + 1) hi
  with ready_in, ready_vals
= ()
```

Committing c changes flux at c only, and c drains into no cell of its own wave.

```pia
let lemma ready_step (down : [usize]) (order : [usize]) (w : usize) (flux : [u32]) (flux2 : [u32])
    (gathered : [u64]) (q : usize) (hi : usize) (c : usize) : unit
  requires len order = len down && len flux = len down && len flux2 = len down && len gathered = len down && q < hi && hi <= len down
  requires forall (r in 0 .. len order). order.[r] < len down
  requires w >= 3 && w < max usize && c < len down
  requires forall (j in 0 .. len down). j = c || flux2.[j] = flux.[j]
  requires forall (r in q + 1 .. hi). at order r <> c && down.[c] <> at order r
  requires ready_in down order w flux gathered q hi
  ensures ready_in down order w flux2 gathered (q + 1) hi
  with ready_in
= frame_all down flux flux2 w c
```

Committing `c` keeps `done_if_upto`.

```pia
let lemma done_if_step (fill : [u16]) (down : [usize]) (acc : [u32]) (bed0 : [u32])
    (bed : [u32]) (flux : [u32]) (seen : [u64]) (bed2 : [u32]) (flux2 : [u32]) (seen2 : [u64]) (pos : [usize]) (p : usize) (c : usize) : unit
  requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill
  requires len seen = len fill && len pos = len fill
  requires len bed2 = len fill && len flux2 = len fill && len seen2 = len fill
  requires c < len fill && pos.[c] = p
  requires forall (j in 0 .. len fill). j = c || (bed2.[j] = bed.[j] && flux2.[j] = flux.[j] && seen2.[j] = seen.[j])
  requires forall (j in 0 .. len fill). at pos j = p ==> j = c
  requires holds_if fill down acc bed0 bed2 flux2 seen2 c
  requires done_if_upto fill down acc bed0 bed flux seen pos p
  ensures done_if_upto fill down acc bed0 bed2 flux2 seen2 pos (p + 1)
  with done_if_upto
= ()
```

Every cell keeps the pull step's promise.

```pia
let spec settled_if (fill : [u16]) (down : [usize]) (acc : [u32]) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) : bool @opaque
  requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill && len seen = len fill
= forall (k in 0 .. len fill). holds_if fill down acc bed0 bed flux seen k
```

The invariants hold at the start.

```pia
let lemma start_pull (fill : [u16]) (down : [usize]) (acc : [u32]) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64])
    (pos : [usize]) (w : usize) : unit
  requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill
  requires len seen = len fill && len pos = len fill && w >= 3 && w < max usize
  ensures done_if_upto fill down acc bed0 bed flux seen pos 0
  ensures linked_upto down flux seen pos 0 w
  with done_if_upto, linked_upto
= ()
```

And give `settled_if` and `linked` at the end.

```pia
let lemma finish_pull (fill : [u16]) (down : [usize]) (acc : [u32]) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64])
    (pos : [usize]) (w : usize) : unit
  requires len down = len fill && len acc = len fill && len bed0 = len fill && len bed = len fill && len flux = len fill
  requires len seen = len fill && len pos = len fill && w >= 3 && w < max usize
  requires forall (k in 0 .. len pos). pos.[k] < len fill
  requires done_if_upto fill down acc bed0 bed flux seen pos (len fill)
  requires linked_upto down flux seen pos (len fill) w
  ensures settled_if fill down acc bed0 bed flux seen
  ensures linked down flux seen w
  with done_if_upto, linked_upto, settled_if, linked
= ()
```

Commits the cell at position q of a wave: its inflow, bed and load.

```pia
let copy_cell (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (gathered : [u64]) (newbed : [u32]) (newout : [u32])
    (bed : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32]) (seen : borrowed inout mutable [u64])
    (q : usize) (lo : usize) (hi : usize) (v : u16) (g : u64) (g0 : u64) : u64
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires w >= 3 && w < max usize && lo <= q && q < hi && hi <= len fill
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len down). down.[k] < len fill
  requires forall (r in lo .. hi). fill.[at order r] = v
  requires done_if_upto fill down acc bed0 bed flux seen pos q
  requires linked_upto down flux seen pos q w
  requires ready_in down order w flux gathered q hi
  requires ready_vals fill down acc order bed0 gathered newbed newout q hi
  requires len fill < max u32 && g0 <= max u32 && g = g0 + osum order down flux q
  ensures result = g0 + osum order down flux (q + 1)
  ensures done_if_upto fill down acc bed0 bed flux seen pos (q + 1)
  ensures linked_upto down flux seen pos (q + 1) w
  ensures ready_in down order w flux gathered (q + 1) hi
  ensures ready_vals fill down acc order bed0 gathered newbed newout (q + 1) hi
=
  let c = order.[q] in
  let d = down.[c] in
  assert pos.[c] = q;
  assert (forall (j in 0 .. len fill). at pos j = q ==> j = c);
  if d <> c then later fill order pos c d else ();
  assert (forall (j in 0 .. len fill). at pos j < q ==> j <> d);
  assert fill.[c] = v;
  assert (forall (r in q + 1 .. hi). at order r <> c && d <> at order r);
  use_ready fill down acc order w bed0 flux gathered newbed newout q hi;
  seen.[c] <- gathered.[q];
  bed.[c] <- newbed.[q];
  flux.[c] <- newout.[q];
  assert holds_if fill down acc bed0 bed flux seen c;
  frame_all down (old flux) flux w c;
  linked_step down (old flux) (old seen) flux seen pos q w c;
  done_if_step fill down acc bed0 (old bed) (old flux) (old seen) bed flux seen pos q c;
  ready_step down order w (old flux) flux gathered q hi c;
  assert (forall (r in 0 .. q). order.[r] <> c);
  osum_frame order down (old flux) flux c q;
  osum_next order down flux q;
  assert oterm order down flux q = (if d = c then flux.[c] else 0);
  let sent : u64 = if d = c then flux.[c] else 0 in
  g + sent
```

Commits one wave, in order.

```pia
let copy_back (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (gathered : [u64]) (newbed : [u32]) (newout : [u32])
    (bed : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32]) (seen : borrowed inout mutable [u64])
    (lo : usize) (hi : usize) (v : u16) (g : u64) (g0 : u64) : u64
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires w >= 3 && w < max usize && lo <= hi && hi <= len fill
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len down). down.[k] < len fill
  requires forall (r in lo .. hi). fill.[at order r] = v
  requires done_if_upto fill down acc bed0 bed flux seen pos lo
  requires linked_upto down flux seen pos lo w
  requires ready_in down order w flux gathered lo hi
  requires ready_vals fill down acc order bed0 gathered newbed newout lo hi
  requires len fill < max u32 && g0 <= max u32 && g = g0 + osum order down flux lo
  ensures result = g0 + osum order down flux hi
  ensures done_if_upto fill down acc bed0 bed flux seen pos hi
  ensures linked_upto down flux seen pos hi w
=
  let g2 : mutable u64 = g in
  for q in lo .. hi
    invariant done_if_upto fill down acc bed0 bed flux seen pos q
    invariant linked_upto down flux seen pos q w
    invariant ready_in down order w flux gathered q hi
    invariant ready_vals fill down acc order bed0 gathered newbed newout q hi
    invariant g2 = g0 + osum order down flux q
  do
    g2 <- copy_cell fill down acc order pos w bed0 gathered newbed newout bed flux seen q lo hi v g2 g0
  done;
  g2
```

The end of the wave that starts at lo: every cell of the same height.

```pia
let wave_end (fill : [u16]) (order : [usize]) (lo : usize) : usize
  requires len order = len fill && lo < len fill
  requires forall (r in 0 .. len order). order.[r] < len fill
  ensures lo < result && result <= len fill
  ensures forall (r in lo .. result). fill.[at order r] = fill.[order.[lo]]
=
  let v = fill.[order.[lo]] in
  let hi : mutable usize = lo + 1 in
  while hi < len fill && fill.[order.[hi]] = v
    invariant lo < hi && hi <= len fill
    invariant forall (r in lo .. hi). fill.[at order r] = v
    decreases len fill - hi
  do
    hi <- hi + 1
  done;
  hi
```

One time step in pull form: wave after wave of equal height, each a spread, then committed in order. It is settled (where the sums fit in a u32) and linked from bed0, and what left the map is the outlets' sum.

```pia
let pull_step (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (bed : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32]) (seen : borrowed inout mutable [u64])
    (gathered : borrowed inout mutable [u64]) (newbed : borrowed inout mutable [u32]) (newout : borrowed inout mutable [u32])
    (gone : u64) : u64
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill
  requires w >= 3 && w < max usize && len fill < max u32 && gone <= max u32
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len down). down.[k] < len fill
  ensures settled_if fill down acc bed0 bed flux seen
  ensures linked down flux seen w
  ensures result = gone + osum order down flux (len fill)
=
  start_pull fill down acc bed0 bed flux seen pos w;
  let g : mutable u64 = gone in
  let lo : mutable usize = 0 in
  while lo < len fill
    invariant lo <= len fill
    invariant done_if_upto fill down acc bed0 bed flux seen pos lo
    invariant linked_upto down flux seen pos lo w
    invariant g = gone + osum order down flux lo
    decreases len fill - lo
  do
    let v = fill.[order.[lo]] in
    let hi = wave_end fill order lo in
    pull_wave fill down acc order w bed0 flux lo hi gathered newbed newout;
    ready_init fill down acc order w bed0 flux gathered newbed newout lo hi;
    g <- copy_back fill down acc order pos w bed0 gathered newbed newout bed flux seen lo hi v g gone;
    lo <- hi
  done;
  finish_pull fill down acc bed0 bed flux seen pos w;
  g
```

```pia

```

## 5. The two steps are the same step

c's upstream neighbours agree in the two loads, so c's inflow does.

```pia
let lemma same_from (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) (fa : [u32]) (fb : [u32]) (w : usize) (c : usize) (d : int{0..7}) : unit
  requires len down = len fill && len order = len fill && len pos = len fill && len fa = len fill && len fb = len fill
  requires c < len fill && w >= 3 && w < max usize
  requires forall (q in 0 .. len order). order.[q] < len pos && pos.[order.[q]] = q
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len fill). pos.[k] < pos.[c] ==> fa.[k] = fb.[k]
  ensures from down fa w c d = from down fb w c d
  with from
= let nb = nbr (len fill) w c d in
  if nb < len fill then (if nb <> c && down.[nb] = c then later fill order pos nb c else ()) else ()
```

Eight equal terms make equal inflows.

```pia
let lemma inflow_eq (down : [usize]) (fa : [u32]) (fb : [u32]) (w : usize) (k : usize) : unit
  requires from down fa w k 0 = from down fb w k 0 && from down fa w k 1 = from down fb w k 1
  requires from down fa w k 2 = from down fb w k 2 && from down fa w k 3 = from down fb w k 3
  requires from down fa w k 4 = from down fb w k 4 && from down fa w k 5 = from down fb w k 5
  requires from down fa w k 6 = from down fb w k 6 && from down fa w k 7 = from down fb w k 7
  ensures inflow_of down fa w k = inflow_of down fb w k
  with inflow_of
= ()
```

```pia
let lemma same_inflow (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) (fa : [u32]) (fb : [u32]) (w : usize) (c : usize) : unit
  requires len down = len fill && len order = len fill && len pos = len fill && len fa = len fill && len fb = len fill
  requires c < len fill && w >= 3 && w < max usize
  requires forall (q in 0 .. len order). order.[q] < len pos && pos.[order.[q]] = q
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len fill). pos.[k] < pos.[c] ==> fa.[k] = fb.[k]
  ensures inflow_of down fa w c = inflow_of down fb w c
= same_from fill down order pos fa fb w c 0; same_from fill down order pos fa fb w c 1;
  same_from fill down order pos fa fb w c 2; same_from fill down order pos fa fb w c 3;
  same_from fill down order pos fa fb w c 4; same_from fill down order pos fa fb w c 5;
  same_from fill down order pos fa fb w c 6; same_from fill down order pos fa fb w c 7;
  inflow_eq down fa fb w c
```

Equal inflow gives equal results, cell by cell.

```pia
let spec determined (ba : [u32]) (fa : [u32]) (sa : [u64]) (bb : [u32]) (fb : [u32]) (sb : [u64]) : bool @opaque
  requires len fa = len sa && len ba = len sa && len bb = len sa && len fb = len sa && len sb = len sa
= forall (k in 0 .. len sa). sa.[k] = sb.[k] ==> fa.[k] = fb.[k] && ba.[k] = bb.[k]
```

The sequential step is settled, the pull step settled where the sums fit; the sequential step's sums always fit, so where the inflow is the same, so is the result.

```pia
let lemma both_if (fill : [u16]) (down : [usize]) (acc : [u32])
    (bed0 : [u32]) (ba : [u32]) (fa : [u32]) (sa : [u64]) (bb : [u32]) (fb : [u32]) (sb : [u64]) : unit
  requires len down = len fill && len acc = len fill
  requires len bed0 = len fill && len ba = len fill && len fa = len fill && len sa = len fill
  requires len bb = len fill && len fb = len fill && len sb = len fill
  requires forall (k in 0 .. len down). down.[k] < len fill
  requires settled fill down acc bed0 ba fa sa && settled_if fill down acc bed0 bb fb sb
  ensures determined ba fa sa bb fb sb
  with settled, settled_if, determined
= ()
```

`determined`, at one cell.

```pia
let lemma use_determined (ba : [u32]) (fa : [u32]) (sa : [u64]) (bb : [u32]) (fb : [u32]) (sb : [u64]) (c : usize) : unit
  requires len fa = len sa && len ba = len sa && len bb = len sa && len fb = len sa && len sb = len sa
  requires c < len sa && determined ba fa sa bb fb sb && sa.[c] = sb.[c]
  ensures fa.[c] = fb.[c] && ba.[c] = bb.[c]
  with determined
= ()
```

`linked`, at one cell.

```pia
let lemma use_linked (down : [usize]) (flux : [u32]) (seen : [u64]) (w : usize) (c : usize) : unit
  requires len flux = len down && len seen = len down && w >= 3 && w < max usize && c < len down
  requires linked down flux seen w
  ensures seen.[c] = inflow_of down flux w c
  with linked
= ()
```

The two steps agree on every cell before position `q` of the order.

```pia
let spec same_upto (pos : [usize]) (ba : [u32]) (fa : [u32]) (bb : [u32]) (fb : [u32]) (q : usize) : bool @opaque
  requires len ba = len pos && len fa = len pos && len bb = len pos && len fb = len pos
= forall (k in 0 .. len pos). at pos k < q ==> fa.[k] = fb.[k] && ba.[k] = bb.[k]
```

Trivially, before position 0.

```pia
let lemma upto_zero (pos : [usize]) (ba : [u32]) (fa : [u32]) (bb : [u32]) (fb : [u32]) : unit
  requires len ba = len pos && len fa = len pos && len bb = len pos && len fb = len pos
  ensures same_upto pos ba fa bb fb 0
  with same_upto
= assert same_upto pos ba fa bb fb 0
```

`same_upto`, unfolded.

```pia
let lemma use_upto (pos : [usize]) (ba : [u32]) (fa : [u32]) (bb : [u32]) (fb : [u32]) (q : usize) : unit
  requires len ba = len pos && len fa = len pos && len bb = len pos && len fb = len pos
  requires same_upto pos ba fa bb fb q
  ensures forall (k in 0 .. len pos). pos.[k] < q ==> fa.[k] = fb.[k] && ba.[k] = bb.[k]
  with same_upto
= ()
```

One more cell.

```pia
let lemma extend (pos : [usize]) (order : [usize]) (ba : [u32]) (fa : [u32]) (bb : [u32]) (fb : [u32]) (c : usize) (q : usize) : unit
  requires len order = len pos && len ba = len pos && len fa = len pos && len bb = len pos && len fb = len pos
  requires q >= 1 && q <= len pos && c < len pos && pos.[c] = q - 1
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires same_upto pos ba fa bb fb (q - 1)
  requires fa.[c] = fb.[c] && ba.[c] = bb.[c]
  ensures same_upto pos ba fa bb fb q
  with same_upto
= assert (forall (k in 0 .. len pos). pos.[k] = q - 1 ==> k = c)
```

Induction along the height order: a cell's upstream neighbours come before it, so by its turn they agree, so its inflow and result do.

```pia
let lemma agree (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize])
    (ba : [u32]) (fa : [u32]) (sa : [u64]) (bb : [u32]) (fb : [u32]) (sb : [u64]) (w : usize) (q : usize) : unit
  requires len down = len fill && len order = len fill && len pos = len fill
  requires len ba = len fill && len fa = len fill && len sa = len fill
  requires len bb = len fill && len fb = len fill && len sb = len fill
  requires w >= 3 && w < max usize && q <= len fill
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires determined ba fa sa bb fb sb
  requires linked down fa sa w && linked down fb sb w
  ensures same_upto pos ba fa bb fb q
  decreases q
= if q > 0 then (
    agree fill down order pos ba fa sa bb fb sb w (q - 1);
    let c = order.[q - 1] in
    assert pos.[c] = q - 1;
    use_upto pos ba fa bb fb (q - 1);
    same_inflow fill down order pos fa fb w c;
    use_linked down fa sa w c;
    use_linked down fb sb w c;
    use_determined ba fa sa bb fb sb c;
    extend pos order ba fa bb fb c q
  ) else upto_zero pos ba fa bb fb
```

The theorem: from the same bed, the pull step and the sequential step leave the same bed and the same loads leaving every cell, cell for cell, and send the same mass off the map.

```pia
let lemma same_step (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (ba : [u32]) (fa : [u32]) (sa : [u64]) (ga : u64) (bb : [u32]) (fb : [u32]) (sb : [u64]) (gb : u64) (gone : u64) : unit
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len ba = len fill && len fa = len fill && len sa = len fill
  requires len bb = len fill && len fb = len fill && len sb = len fill
  requires w >= 3 && w < max usize && len fill <= max u32
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len down). down.[k] < len fill
  requires settled fill down acc bed0 ba fa sa && linked down fa sa w
  requires settled_if fill down acc bed0 bb fb sb && linked down fb sb w
  requires ga = gone + osum order down fa (len fill) && gb = gone + osum order down fb (len fill)
  ensures forall (k in 0 .. len fill). ba.[k] = bb.[k] && fa.[k] = fb.[k]
  ensures ga = gb
= both_if fill down acc bed0 ba fa sa bb fb sb;
  agree fill down order pos ba fa sa bb fb sb w (len fill);
  use_upto pos ba fa bb fb (len fill);
  assert (forall (k in 0 .. len fill). pos.[k] < len fill);
  osum_eq order down fa fb (len fill)
```
Both steps, from the same bed. The postcondition is the theorem: `same_step`
turns their own postconditions into it.

```pia
let both_steps (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (bed_s : borrowed inout mutable [u32]) (load : borrowed inout mutable [u32]) (inflow : borrowed inout mutable [u32])
    (flux_s : borrowed inout mutable [u32]) (seen_s : borrowed inout mutable [u64])
    (bed_p : borrowed inout mutable [u32]) (flux_p : borrowed inout mutable [u32]) (seen_p : borrowed inout mutable [u64])
    (gathered : borrowed inout mutable [u64]) (newbed : borrowed inout mutable [u32]) (newout : borrowed inout mutable [u32])
    (gone : u64) : u64
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len bed_s = len fill && len load = len fill && len inflow = len fill && len flux_s = len fill && len seen_s = len fill
  requires len bed_p = len fill && len flux_p = len fill && len seen_p = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill
  requires w >= 3 && w < max usize && len fill < max u32 && gone <= max u32
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len down). down.[k] < len fill
  requires forall (k in 0 .. len down). down.[k] = k || adjacent w k (down.[k])
  requires forall (k in 0 .. len fill). load.[k] = 0 && inflow.[k] = 0 && bed_s.[k] = bed0.[k]
  requires sum bed_s (len bed_s) + sum load (len load) + sum inflow (len inflow) + gone <= max u32
  ensures forall (k in 0 .. len fill). bed_s.[k] = bed_p.[k] && flux_s.[k] = flux_p.[k]
=
  let ga = transport_seen fill down acc order pos w bed0 bed_s load inflow flux_s seen_s gone in
  let gb = pull_step fill down acc order pos w bed0 bed_p flux_p seen_p gathered newbed newout gone in
  same_step fill down acc order pos w bed0 bed_s flux_s seen_s ga bed_p flux_p seen_p gb gone;
  gb
```

## What is proved

| Goal | Where |
| --- | --- |
| The pull step and the sequential step leave the same bed and loads, and send the same mass off the map | `same_step`, `both_steps` |
| The sequential step is settled and linked, and conserves mass | `transport_seen`, through `seq_cell` |
| The pull step is settled where its sums fit, and linked | `pull_step`, through `pull_wave` and `copy_back` |
| Each wave is a race-free `spread`: every iteration writes only its own slots | `pull_wave` (ADR 0060's ownership check) |
| Two settled, linked steps from the same bed are the same | `agree`, by induction along the height order |
| Every index is in bounds, nothing overflows, every loop ends | every function |

D8 directions point at a neighbour, which the sequential step needs: it
is `directions`'s postcondition in [streams.pia.md](streams.pia.md).
