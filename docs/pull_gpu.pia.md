# Demo: the sediment pull step on the GPU

The [pull step](pull.pia.md) takes the cells in waves, one for each
height. Every cell of a wave reads its eight neighbours, adds the loads of
those that drain into it, and erodes or deposits, writing only its own
slots of three scratch buffers. A short pass then commits the wave in
order. Here the whole step runs on the GPU as one placed sequence
([ADR 0068, section 9](adr/0068-gpu-compute-through-spirv-and-metal.md)):
the `for` over the waves carries `@place(gpu)`, so each wave and each
commit becomes one dispatch, all of them in one command buffer. The
buffers are wrapped once and the host commits once and waits once. On a
Mac the GPU and the CPU share memory, so no buffer is copied.

The step is still proved. Its postcondition is `pull_step`'s: the step is
settled where the sums fit in a `u32`, it is linked, and what left the map
is the outlets' sum. That is all `same_step` in pull.pia.md needs, so when
the sequence returns `Ok`, the GPU step is the sequential step, cell for
cell. The specification of the step is not repeated: this page imports it,
with the lemmas that start and finish a step, through the interface
`PullWaves` that pull.pia.md provides. The wave, the commit (now a spread
of its own) and the table of where each wave starts are new.

A placed sequence is fallible ([ADR 0068, section
5](adr/0068-gpu-compute-through-spirv-and-metal.md)): it evaluates to
`result unit gpu_error`, and its invariants hold after it only when it
returns `Ok`. So the step returns a `result`. On an error the buffers may
be part written, and nothing is promised about them.

```pia
module PullGpu : PullGpuStep

import Pull.PullWaves as P

interface PullGpuStep @abi(c) = sig
  let pull_step_gpu : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (order : [usize])
      -> (pos : [usize]) -> (w : usize) -> (bed0 : [u32])
      -> (bed : borrowed inout mutable [u32]) -> (flux : borrowed inout mutable [u32])
      -> (seen : borrowed inout mutable [u64]) -> (gathered : borrowed inout mutable [u64])
      -> (newbed : borrowed inout mutable [u32]) -> (newout : borrowed inout mutable [u32])
      -> (starts : borrowed inout mutable [usize]) -> (gone : u64) -> (sent : out mutable [u64]) -> i32
    requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
    requires len bed = len fill && len flux = len fill && len seen = len fill
    requires len gathered = len fill && len newbed = len fill && len newout = len fill && len starts = len fill + 1
    requires w >= 3 && w < max usize && len fill < max u32 && gone <= max u32 && len sent = 1
    requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
    requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
    requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
    requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
    requires forall (k in 0 .. len down). down.[k] < len fill
end
```

## 1. One cell's inflow

The GPU has no call stack, so piac inlines every call in a placed body,
and a body may call only functions of its own module. These are
pull.pia.md's, again: the neighbour in a direction, the load it sends, and
the sum of all eight as a tree of two-term sums. Each says it computes the
specification function of the same name in `PullWaves`, so what the
kernel computes is what the commit pass expects.

```pia
let before (n : usize) (w : usize) (c : usize) (d : usize) : usize
  requires w >= 3 && w < max usize && c < n && (d = 1 || d = w - 1 || d = w || d = w + 1)
  ensures result = (if c >= d then c - d else n)
= if c >= d then c - d else n

let after (n : usize) (w : usize) (c : usize) (d : usize) : usize
  requires w >= 3 && w < max usize && c < n && (d = 1 || d = w - 1 || d = w || d = w + 1)
  ensures result = (if d < n - c then c + d else n)
= if d < n - c then c + d else n

let neighbour (n : usize) (w : usize) (c : usize) (d : int{0..7}) : usize
  requires w >= 3 && w < max usize && c < n
  ensures result = P.nbr n w c d
=
  if d = 0 then before n w c (w + 1)
  else if d = 1 then before n w c w
  else if d = 2 then before n w c (w - 1)
  else if d = 3 then before n w c 1
  else if d = 4 then after n w c 1
  else if d = 5 then after n w c (w - 1)
  else if d = 6 then after n w c w
  else after n w c (w + 1)

let pull_from (down : [usize]) (flux : [u32]) (w : usize) (c : usize) (d : int{0..7}) : u64
  requires len flux = len down && c < len down && w >= 3 && w < max usize
  ensures result = P.from down flux w c d
  with P.from
= let nb = neighbour (len down) w c d in
  if nb < len down then (if nb <> c && down.[nb] = c then flux.[nb] else 0) else 0

let gather (down : [usize]) (flux : [u32]) (w : usize) (c : usize) : u64
  requires len flux = len down && c < len down && w >= 3 && w < max usize
  ensures result = P.inflow_of down flux w c
  with P.inflow_of
= let a = pull_from down flux w c 0 + pull_from down flux w c 1 in
  let b = pull_from down flux w c 2 + pull_from down flux w c 3 in
  let e = pull_from down flux w c 4 + pull_from down flux w c 5 in
  let f = pull_from down flux w c 6 + pull_from down flux w c 7 in
  (a + b) + (e + f)
```

## 2. Erosion and deposition, in scalars

A record is not one of the values a placed body may hold yet, so the
`cell` that pull.pia.md's `erode_or_deposit` returns becomes two
functions, one for the bed left and one for the load sent on.

The capacity of a cell, from its flow and its drop.

```pia
let capacity_of (a : u32) (drop : u16) : u32
  ensures result = P.cap_rule a drop
=
  let d : u32 = drop in
  let c : u64 = (a >> 4) + (d << 2) in
  if c < max u16 then c else max u16
```

The bed a cell is left with, from inflow `i`, capacity `cap` and bed `bed`:
below capacity it erodes as much as it can carry, and above it deposits
the excess.

```pia
let bed_after (i : u64) (cap : u32) (bed : u32) : u32
  requires i + bed <= max u32
  ensures result = P.eb i cap bed
= if i < cap then (let room = cap - i in if room < bed then bed - room else 0)
  else bed + (i - cap)
```

The load it sends on.

```pia
let load_after (i : u64) (cap : u32) (bed : u32) : u32
  requires i + bed <= max u32
  ensures result = P.el i cap bed
= if i < cap then (let room = cap - i in if room < bed then cap else i + bed)
  else cap
```

## 3. A wave

The cells at positions `lo .. hi` of the height order, one thread each.
Thread `q` writes only slot `q` of `gathered`, `newbed` and `newout`, the
identity ownership of a spread, and every slot then holds what `ready_init`
in pull.pia.md asks of a wave.

```pia
let wave (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (w : usize)
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
  ensures forall (q in lo .. hi). gathered.[q] = P.inflow_of down flux w (order.[q])
  ensures forall (q in lo .. hi). gathered.[q] + bed0.[order.[q]] <= max u32 ==>
    newbed.[q] = P.eb (gathered.[q]) (P.cap_of fill down acc (order.[q])) (bed0.[order.[q]])
    && newout.[q] = P.el (gathered.[q]) (P.cap_of fill down acc (order.[q])) (bed0.[order.[q]])
= spread q in lo .. hi
    ensures gathered.[q] = P.inflow_of down flux w (order.[q])
    ensures gathered.[q] + bed0.[order.[q]] <= max u32 ==>
      newbed.[q] = P.eb (gathered.[q]) (P.cap_of fill down acc (order.[q])) (bed0.[order.[q]])
      && newout.[q] = P.el (gathered.[q]) (P.cap_of fill down acc (order.[q])) (bed0.[order.[q]])
  do
    let c = order.[q] in
    let g = gather down flux w c in
    gathered.[q] <- g;
    let b = bed0.[c] in
    let d = down.[c] in
    let drop : u16 = if d = c then 0 else fill.[c] - fill.[d] in
    if g + b <= max u32 then (
      let cap = capacity_of acc.[c] drop in
      newbed.[q] <- bed_after g cap b;
      newout.[q] <- load_after g cap b
    ) else (
      newbed.[q] <- b;
      newout.[q] <- 0
    )
  done
```

## 4. Its commit, on the GPU too

pull.pia.md commits a wave one cell at a time, in order. Here the commit is
a spread as well: thread `q` writes cell `order.[q]` of `bed`, `flux` and
`seen`, and `pos` is the owner array that says so, since
`pos.[order.[q]] = q` (`@owns`, ADR 0060). After the spread, the cells of
other waves keep their values, because no thread of this wave owns them.

The commit keeps the step's two invariants, for the whole wave at once.
What makes that true is that a wave is one height. Every cell of the wave
drains into a lower cell or into itself, so no cell processed so far,
which is at that height or higher, reads a load the wave changed.

A load that changes only at cells of height `v` leaves the inflow of every
cell at height `v` or higher as it was, one direction at a time:

```pia
let lemma wframe_dir (fill : [u16]) (down : [usize]) (flux : [u32]) (flux2 : [u32]) (w : usize) (v : u16) (d : int{0..7}) : unit
  requires len fill = len down && len flux = len down && len flux2 = len down && w >= 3 && w < max usize
  requires forall (k in 0 .. len down). down.[k] < len down && (down.[k] = k || fill.[down.[k]] < fill.[k])
  requires forall (j in 0 .. len down). flux2.[j] = flux.[j] || fill.[j] = v
  ensures forall (k in 0 .. len down). fill.[k] >= v ==> P.from down flux2 w k d = P.from down flux w k d
  with P.from
= ()

let lemma wframe_pair (fill : [u16]) (down : [usize]) (flux : [u32]) (flux2 : [u32]) (w : usize) (v : u16) (h : int{0..3}) : unit
  requires len fill = len down && len flux = len down && len flux2 = len down && w >= 3 && w < max usize
  requires forall (k in 0 .. len down). down.[k] < len down && (down.[k] = k || fill.[down.[k]] < fill.[k])
  requires forall (j in 0 .. len down). flux2.[j] = flux.[j] || fill.[j] = v
  ensures forall (k in 0 .. len down). fill.[k] >= v ==> P.pair down flux2 w k h = P.pair down flux w k h
= if h = 0 then (wframe_dir fill down flux flux2 w v 0; wframe_dir fill down flux flux2 w v 1)
  else if h = 1 then (wframe_dir fill down flux flux2 w v 2; wframe_dir fill down flux flux2 w v 3)
  else if h = 2 then (wframe_dir fill down flux flux2 w v 4; wframe_dir fill down flux flux2 w v 5)
  else (wframe_dir fill down flux flux2 w v 6; wframe_dir fill down flux flux2 w v 7)

let lemma wframe_all (fill : [u16]) (down : [usize]) (flux : [u32]) (flux2 : [u32]) (w : usize) (v : u16) : unit
  requires len fill = len down && len flux = len down && len flux2 = len down && w >= 3 && w < max usize
  requires forall (k in 0 .. len down). down.[k] < len down && (down.[k] = k || fill.[down.[k]] < fill.[k])
  requires forall (j in 0 .. len down). flux2.[j] = flux.[j] || fill.[j] = v
  ensures forall (k in 0 .. len down). fill.[k] >= v ==> P.inflow_of down flux2 w k = P.inflow_of down flux w k
  with P.inflow_of
= wframe_pair fill down flux flux2 w v 0; wframe_pair fill down flux flux2 w v 1;
  wframe_pair fill down flux flux2 w v 2; wframe_pair fill down flux flux2 w v 3
```

Every cell processed by the end of the wave is at height `v` or higher:

```pia
let lemma above (fill : [u16]) (order : [usize]) (pos : [usize]) (lo : usize) (hi : usize) (v : u16) : unit
  requires len order = len fill && len pos = len fill && lo < hi && hi <= len fill
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (r in lo .. hi). fill.[P.at order r] = v
  ensures forall (k in 0 .. len fill). P.at pos k < hi ==> fill.[k] >= v
=
  assert fill.[order.[lo]] = v;
  assert (forall (k in 0 .. len fill). P.at pos k < lo ==> fill.[order.[lo]] <= fill.[order.[P.at pos k]]);
  assert (forall (k in 0 .. len fill). P.at pos k < hi ==> order.[P.at pos k] = k)
```

The cells the commit changed are the wave's, which are at height `v`:

```pia
let lemma changed_in_wave (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (gathered : [u64]) (newbed : [u32]) (newout : [u32])
    (bed : [u32]) (flux : [u32]) (seen : [u64]) (bed2 : [u32]) (flux2 : [u32]) (seen2 : [u64])
    (lo : usize) (hi : usize) (v : u16) : unit
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires len bed2 = len fill && len flux2 = len fill && len seen2 = len fill
  requires w >= 3 && w < max usize && lo < hi && hi <= len fill
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (r in lo .. hi). fill.[P.at order r] = v
  requires forall (q in lo .. hi). seen2.[P.at order q] = gathered.[q] && bed2.[P.at order q] = newbed.[q] && flux2.[P.at order q] = newout.[q]
  requires forall (k in 0 .. len fill). (P.at pos k < lo || P.at pos k >= hi) ==>
    bed2.[k] = bed.[k] && flux2.[k] = flux.[k] && seen2.[k] = seen.[k]
  ensures forall (j in 0 .. len fill). flux2.[j] = flux.[j] || fill.[j] = v
  ensures forall (j in 0 .. len fill). (lo <= P.at pos j && P.at pos j < hi) ==> P.at order (P.at pos j) = j
=
  assert (forall (j in 0 .. len fill). (lo <= P.at pos j && P.at pos j < hi) ==> P.at order (P.at pos j) = j);
  assert (forall (j in 0 .. len fill). (lo <= P.at pos j && P.at pos j < hi) ==> fill.[j] = v)
```

The committed cells keep the step's promise, `holds_if`:

```pia
let lemma done_commit (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (gathered : [u64]) (newbed : [u32]) (newout : [u32])
    (bed : [u32]) (flux : [u32]) (seen : [u64]) (bed2 : [u32]) (flux2 : [u32]) (seen2 : [u64])
    (lo : usize) (hi : usize) (v : u16) : unit
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires len bed2 = len fill && len flux2 = len fill && len seen2 = len fill
  requires w >= 3 && w < max usize && lo < hi && hi <= len fill
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (q in lo .. hi). seen2.[P.at order q] = gathered.[q] && bed2.[P.at order q] = newbed.[q] && flux2.[P.at order q] = newout.[q]
  requires forall (k in 0 .. len fill). (P.at pos k < lo || P.at pos k >= hi) ==>
    bed2.[k] = bed.[k] && flux2.[k] = flux.[k] && seen2.[k] = seen.[k]
  requires P.done_if_upto fill down acc bed0 bed flux seen pos lo
  requires P.ready_vals fill down acc order bed0 gathered newbed newout lo hi
  ensures P.done_if_upto fill down acc bed0 bed2 flux2 seen2 pos hi
  with P.done_if_upto, P.ready_vals
=
  assert (forall (j in 0 .. len fill). (lo <= P.at pos j && P.at pos j < hi) ==> P.at order (P.at pos j) = j)
```

And they are linked: each took its upstream neighbours' loads.

```pia
let lemma linked_commit (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (gathered : [u64]) (newbed : [u32]) (newout : [u32])
    (bed : [u32]) (flux : [u32]) (seen : [u64]) (bed2 : [u32]) (flux2 : [u32]) (seen2 : [u64])
    (lo : usize) (hi : usize) (v : u16) : unit
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires len bed2 = len fill && len flux2 = len fill && len seen2 = len fill
  requires w >= 3 && w < max usize && lo < hi && hi <= len fill
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] < len fill && (down.[k] = k || fill.[down.[k]] < fill.[k])
  requires forall (r in lo .. hi). fill.[P.at order r] = v
  requires forall (q in lo .. hi). seen2.[P.at order q] = gathered.[q] && bed2.[P.at order q] = newbed.[q] && flux2.[P.at order q] = newout.[q]
  requires forall (k in 0 .. len fill). (P.at pos k < lo || P.at pos k >= hi) ==>
    bed2.[k] = bed.[k] && flux2.[k] = flux.[k] && seen2.[k] = seen.[k]
  requires P.linked_upto down flux seen pos lo w
  requires P.ready_in down order w flux gathered lo hi
  requires forall (j in 0 .. len fill). flux2.[j] = flux.[j] || fill.[j] = v
  requires forall (j in 0 .. len fill). (lo <= P.at pos j && P.at pos j < hi) ==> P.at order (P.at pos j) = j
  ensures P.linked_upto down flux2 seen2 pos hi w
  with P.linked_upto, P.ready_in
=
  wframe_all fill down flux flux2 w v;
  above fill order pos lo hi v

let lemma committed (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (gathered : [u64]) (newbed : [u32]) (newout : [u32])
    (bed : [u32]) (flux : [u32]) (seen : [u64]) (bed2 : [u32]) (flux2 : [u32]) (seen2 : [u64])
    (lo : usize) (hi : usize) (v : u16) : unit
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires len bed2 = len fill && len flux2 = len fill && len seen2 = len fill
  requires w >= 3 && w < max usize && lo < hi && hi <= len fill
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] < len fill && (down.[k] = k || fill.[down.[k]] < fill.[k])
  requires forall (r in lo .. hi). fill.[P.at order r] = v
  requires P.done_if_upto fill down acc bed0 bed flux seen pos lo
  requires P.linked_upto down flux seen pos lo w
  requires P.ready_in down order w flux gathered lo hi
  requires P.ready_vals fill down acc order bed0 gathered newbed newout lo hi
  requires forall (q in lo .. hi). seen2.[P.at order q] = gathered.[q] && bed2.[P.at order q] = newbed.[q] && flux2.[P.at order q] = newout.[q]
  requires forall (k in 0 .. len fill). (P.at pos k < lo || P.at pos k >= hi) ==>
    bed2.[k] = bed.[k] && flux2.[k] = flux.[k] && seen2.[k] = seen.[k]
  ensures P.done_if_upto fill down acc bed0 bed2 flux2 seen2 pos hi
  ensures P.linked_upto down flux2 seen2 pos hi w
=
  changed_in_wave fill down acc order pos w bed0 gathered newbed newout bed flux seen bed2 flux2 seen2 lo hi v;
  done_commit fill down acc order pos w bed0 gathered newbed newout bed flux seen bed2 flux2 seen2 lo hi v;
  linked_commit fill down acc order pos w bed0 gathered newbed newout bed flux seen bed2 flux2 seen2 lo hi v
```

The commit itself:

```pia
let commit (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (gathered : [u64]) (newbed : [u32]) (newout : [u32])
    (bed : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32]) (seen : borrowed inout mutable [u64])
    (lo : usize) (hi : usize) (v : u16) : unit
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires w >= 3 && w < max usize && lo < hi && hi <= len fill
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] < len fill && (down.[k] = k || fill.[down.[k]] < fill.[k])
  requires forall (r in lo .. hi). fill.[P.at order r] = v
  requires P.done_if_upto fill down acc bed0 bed flux seen pos lo
  requires P.linked_upto down flux seen pos lo w
  requires P.ready_in down order w flux gathered lo hi
  requires P.ready_vals fill down acc order bed0 gathered newbed newout lo hi
  ensures P.done_if_upto fill down acc bed0 bed flux seen pos hi
  ensures P.linked_upto down flux seen pos hi w
=
  spread q in lo .. hi @owns(bed, pos) @owns(flux, pos) @owns(seen, pos)
    ensures seen.[order.[q]] = gathered.[q] && bed.[order.[q]] = newbed.[q] && flux.[order.[q]] = newout.[q]
  do
    let c = order.[q] in
    seen.[c] <- gathered.[q];
    bed.[c] <- newbed.[q];
    flux.[c] <- newout.[q]
  done;
  committed fill down acc order pos w bed0 gathered newbed newout (old bed) (old flux) (old seen) bed flux seen lo hi v
```

## 5. The step, as one command buffer

The waves of a step are found first, on the CPU. A wave is a run of
positions of one height, so the scan writes where each one starts:

```pia
let spec wave_at (fill : [u16]) (order : [usize]) (lo : usize) (hi : usize) : bool @opaque
  requires len order = len fill
  requires forall (r in 0 .. len order). order.[r] < len fill
= lo < hi && hi <= len fill
  && (forall (r in lo .. hi). fill.[P.at order r] = fill.[P.at order lo])

let lemma use_wave (fill : [u16]) (order : [usize]) (lo : usize) (hi : usize) : unit
  requires len order = len fill
  requires forall (r in 0 .. len order). order.[r] < len fill
  requires wave_at fill order lo hi
  ensures lo < hi && hi <= len fill
  ensures forall (r in lo .. hi). fill.[P.at order r] = fill.[P.at order lo]
  with wave_at
= ()

let lemma close_wave (fill : [u16]) (order : [usize]) (lo : usize) (hi : usize) : unit
  requires len order = len fill
  requires forall (r in 0 .. len order). order.[r] < len fill
  requires lo < hi && hi <= len fill
  requires forall (r in lo .. hi). fill.[P.at order r] = fill.[P.at order lo]
  ensures wave_at fill order lo hi
  with wave_at
= ()

let wave_starts (fill : [u16]) (order : [usize]) (starts : borrowed inout mutable [usize]) : usize
  requires len order = len fill && len starts = len fill + 1 && len fill > 0
  requires forall (r in 0 .. len order). order.[r] < len fill
  ensures 1 <= result && result <= len fill
  ensures starts.[0] = 0 && starts.[result] = len fill
  ensures forall (k in 0 .. result). wave_at fill order (starts.[k]) (starts.[k + 1])
=
  starts.[0] <- 0;
  let m : mutable usize = 0 in
  for r in 1 .. len fill
    invariant m < r && starts.[0] = 0 && starts.[m] < r
    invariant forall (t in starts.[m] .. r). fill.[P.at order t] = fill.[P.at order (starts.[m])]
    invariant forall (k in 0 .. m). wave_at fill order (starts.[k]) (starts.[k + 1])
  do
    if fill.[order.[r]] <> fill.[order.[r - 1]] then (
      let lo = starts.[m] in
      close_wave fill order lo r;
      starts.[m + 1] <- r;
      m <- m + 1
    ) else ()
  done;
  let lo = starts.[m] in
  close_wave fill order lo (len fill);
  starts.[m + 1] <- len fill;
  m + 1
```

The mass the step sends off the map is the outlets' loads, added in height
order, after the step:

```pia
let out_sum (order : [usize]) (down : [usize]) (flux : [u32]) : u64
  requires len down = len order && len flux = len order && len order < max u32
  requires forall (r in 0 .. len order). order.[r] < len order
  ensures result = P.osum order down flux (len order)
=
  let s : mutable u64 = 0 in
  for q in 0 .. len order
    invariant s = P.osum order down flux q
  do
    P.osum_next order down flux q;
    let c = order.[q] in
    let t : u32 = if down.[c] = c then flux.[c] else 0 in
    s <- s + t
  done;
  s
```

Then the step is one sequential `for` over the waves with `@place(gpu)`
on it ([ADR 0068, section
9](adr/0068-gpu-compute-through-spirv-and-metal.md)). Each iteration's two
spreads, which piac finds through the calls of `wave` and `commit`, become
two dispatches. The host runs the rest of the body as it encodes them: it
reads the bounds from `starts`, which no kernel writes, and the lemma calls
leave no code. So the whole step is one command buffer, with the buffers
wrapped once and one wait. Its invariants are the ones `pull_step` keeps,
so on `Ok` its postcondition is `pull_step`'s.

```pia
let pull_step_on_gpu (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (bed : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32]) (seen : borrowed inout mutable [u64])
    (gathered : borrowed inout mutable [u64]) (newbed : borrowed inout mutable [u32]) (newout : borrowed inout mutable [u32])
    (starts : borrowed inout mutable [usize]) (gone : u64) : result u64 gpu_error
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill && len starts = len fill + 1
  requires w >= 3 && w < max usize && len fill < max u32 && gone <= max u32
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len down). down.[k] < len fill
  ensures (match result with
           | Ok s -> P.settled_if fill down acc bed0 bed flux seen && P.linked down flux seen w
                     && s = gone + P.osum order down flux (len fill)
           | Err _ -> true)
=
  P.start_pull fill down acc bed0 bed flux seen pos w;
  if len fill = 0 then (P.finish_pull fill down acc bed0 bed flux seen pos w; Ok gone)
  else (
    let waves = wave_starts fill order starts in
    let run =
      for k in 0 .. waves @place(gpu)
        invariant P.done_if_upto fill down acc bed0 bed flux seen pos (starts.[k])
        invariant P.linked_upto down flux seen pos (starts.[k]) w
      do
        let lo = starts.[k] in
        let hi = starts.[k + 1] in
        use_wave fill order lo hi;
        wave fill down acc order w bed0 flux lo hi gathered newbed newout;
        P.ready_init fill down acc order w bed0 flux gathered newbed newout lo hi;
        commit fill down acc order pos w bed0 gathered newbed newout bed flux seen lo hi (fill.[order.[lo]])
      done
    in
    match run with
    | Ok -> (P.finish_pull fill down acc bed0 bed flux seen pos w; Ok (gone + out_sum order down flux))
    | Err e -> Err e)
```

Its C entry point: 0 with the mass sent off the map in `sent.[0]`, or 1
plus the `gpu_error`, in its order. `starts` is scratch, one more than the
cells.

```pia
let pull_step_gpu (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (bed : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32]) (seen : borrowed inout mutable [u64])
    (gathered : borrowed inout mutable [u64]) (newbed : borrowed inout mutable [u32]) (newout : borrowed inout mutable [u32])
    (starts : borrowed inout mutable [usize]) (gone : u64) (sent : out mutable [u64]) : i32
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill && len starts = len fill + 1
  requires w >= 3 && w < max usize && len fill < max u32 && gone <= max u32 && len sent = 1
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len down). down.[k] < len fill
=
  match pull_step_on_gpu fill down acc order pos w bed0 bed flux seen gathered newbed newout starts gone with
  | Ok s -> (sent.[0] <- s; 0)
  | Err e ->
    (match e with
     | Gpu_unavailable -> 1
     | Gpu_out_of_memory -> 2
     | Gpu_fault -> 3
     | Gpu_timeout -> 4)
```

## How fast it is, so far

With a dispatch per wave and a command buffer each, the step was correct
but slow: on the whole tile N46E008 (3601 × 3601 cells, 3,924 waves a step)
it took 33 to 57 s a step against 0.5 s on the CPU, nearly all of it
wrapping buffers and waiting for each command buffer. The placed sequence
on this page pays those costs once a step. Its timings come with the
compiler support for `@place(gpu)` on a `for`.

## What is proved, and what is checked

| Claim | Where |
| --- | --- |
| When the sequence returns `Ok`, the GPU step is settled and linked, and sends the outlets' sum off the map | `pull_step_on_gpu` |
| So it is the sequential step, cell for cell | `same_step` in [pull.pia.md](pull.pia.md), whose premises these are |
| Each thread writes only its own slots | the ownership check of ADR 0060 |
| A thread computes each cell's inflow, bed and load as the specification says | `gather`, `bed_after`, `load_after`, in the spread's `ensures` |
| Every index is in bounds and nothing overflows | every function |
| The toolchain from SPIR-V to Metal keeps the kernel's meaning | `srtm_gpu`, a differential test against `pull_step` (ADR 0068, section 6) |
