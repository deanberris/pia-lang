# Demo: the sediment pull step on the GPU

The [pull step](pull.pia.md) takes the cells in waves, one for each
height. Every cell of a wave reads its eight neighbours, adds the loads of
those that drain into it, and erodes or deposits, writing only its own
slots of three scratch buffers. A short pass then commits the wave in
order. Here each wave runs on the GPU: its spread is placed with
`@place(gpu)` ([ADR 0068](adr/0068-gpu-compute-through-spirv-and-metal.md)),
so one wave is one dispatch, one thread per cell. The commit pass stays on
the CPU, where it is cheap. On a Mac the two share memory, so neither
copies a buffer.

The step is still proved. Its postcondition is `pull_step`'s: the step is
settled where the sums fit in a `u32`, it is linked, and what left the map
is the outlets' sum. That is all `same_step` in pull.pia.md needs, so when
every wave returns `Ok`, the GPU step is the sequential step, cell for
cell. The proof of the commit pass is not repeated: this page imports it,
with the specification functions it is written in, through the interface
`PullWaves` that pull.pia.md provides. Only the wave is new.

A placed spread is fallible ([ADR 0068, section
5](adr/0068-gpu-compute-through-spirv-and-metal.md)): it evaluates to
`result unit gpu_error`, and its `ensures` holds only when it returns
`Ok`. So the step returns a `result`, and the first wave that fails ends
it with that error. The buffers may then be part written, and nothing is
promised about them.

```pia
module PullGpu : PullGpuStep

import Pull.PullWaves as P

interface PullGpuStep @abi(c) = sig
  let pull_step_gpu : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (order : [usize])
      -> (pos : [usize]) -> (w : usize) -> (bed0 : [u32])
      -> (bed : borrowed inout mutable [u32]) -> (flux : borrowed inout mutable [u32])
      -> (seen : borrowed inout mutable [u64]) -> (gathered : borrowed inout mutable [u64])
      -> (newbed : borrowed inout mutable [u32]) -> (newout : borrowed inout mutable [u32])
      -> (gone : u64) -> (sent : out mutable [u64]) -> i32
    requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
    requires len bed = len fill && len flux = len fill && len seen = len fill
    requires len gathered = len fill && len newbed = len fill && len newout = len fill
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

## 3. A wave on the GPU

The cells at positions `lo .. hi` of the height order, one thread each.
Thread `q` writes only slot `q` of `gathered`, `newbed` and `newout`, the
identity ownership of a spread, and when the run returns `Ok` every slot
holds what `ready_init` in pull.pia.md asks of a wave.

```pia
let pull_wave_on_gpu (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (w : usize)
    (bed0 : [u32]) (flux : [u32]) (lo : usize) (hi : usize)
    (gathered : borrowed inout mutable [u64]) (newbed : borrowed inout mutable [u32])
    (newout : borrowed inout mutable [u32]) : result unit gpu_error
  requires len down = len fill && len acc = len fill && len order = len fill
  requires len bed0 = len fill && len flux = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill
  requires lo <= hi && hi <= len fill && w >= 3 && w < max usize
  requires forall (q in 0 .. len order). order.[q] < len fill
  requires forall (k in 0 .. len down). down.[k] < len fill
  requires forall (k in 0 .. len down). down.[k] = k || fill.[down.[k]] < fill.[k]
  ensures (match result with
           | Ok () ->
             (forall (q in lo .. hi). gathered.[q] = P.inflow_of down flux w (order.[q]))
             && (forall (q in lo .. hi). gathered.[q] + bed0.[order.[q]] <= max u32 ==>
                  newbed.[q] = P.eb (gathered.[q]) (P.cap_of fill down acc (order.[q])) (bed0.[order.[q]])
                  && newout.[q] = P.el (gathered.[q]) (P.cap_of fill down acc (order.[q])) (bed0.[order.[q]]))
           | Err _ -> true)
= spread q in lo .. hi @place(gpu)
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

## 4. The step

Wave after wave, as `pull_step` in pull.pia.md: the wave on the GPU, then
its commit on the CPU, with the same invariants. The first wave that fails
ends the step with its error. A `?` cannot leave a loop yet, so the loop
stops on its own, which the extra 1 in its measure accounts for.

```pia
let pull_step_on_gpu (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (bed : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32]) (seen : borrowed inout mutable [u64])
    (gathered : borrowed inout mutable [u64]) (newbed : borrowed inout mutable [u32]) (newout : borrowed inout mutable [u32])
    (gone : u64) : result u64 gpu_error
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill
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
  let g : mutable u64 = gone in
  let lo : mutable usize = 0 in
  let failed : mutable bool = false in
  let why : mutable gpu_error = Gpu_fault in
  while lo < len fill && failed = false
    invariant lo <= len fill
    invariant P.done_if_upto fill down acc bed0 bed flux seen pos lo
    invariant P.linked_upto down flux seen pos lo w
    invariant g = gone + P.osum order down flux lo
    decreases len fill - lo + (if failed then 0 else 1)
  do
    let v = fill.[order.[lo]] in
    let hi = P.wave_end fill order lo in
    match pull_wave_on_gpu fill down acc order w bed0 flux lo hi gathered newbed newout with
    | Ok () ->
      (P.ready_init fill down acc order w bed0 flux gathered newbed newout lo hi;
       g <- P.copy_back fill down acc order pos w bed0 gathered newbed newout bed flux seen lo hi v g gone;
       lo <- hi)
    | Err e -> (failed <- true; why <- e)
  done;
  if failed then Err why
  else (P.finish_pull fill down acc bed0 bed flux seen pos w; Ok g)
```

Its C entry point: 0 with the mass sent off the map in `sent.[0]`, or 1
plus the `gpu_error`, in its order.

```pia
let pull_step_gpu (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (bed : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32]) (seen : borrowed inout mutable [u64])
    (gathered : borrowed inout mutable [u64]) (newbed : borrowed inout mutable [u32]) (newout : borrowed inout mutable [u32])
    (gone : u64) (sent : out mutable [u64]) : i32
  requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires len gathered = len fill && len newbed = len fill && len newout = len fill
  requires w >= 3 && w < max usize && len fill < max u32 && gone <= max u32 && len sent = 1
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len down). down.[k] < len fill
=
  match pull_step_on_gpu fill down acc order pos w bed0 bed flux seen gathered newbed newout gone with
  | Ok s -> (sent.[0] <- s; 0)
  | Err e ->
    (match e with
     | Gpu_unavailable -> 1
     | Gpu_out_of_memory -> 2
     | Gpu_fault -> 3
     | Gpu_timeout -> 4)
```

## How fast it is, so far

Correct, not fast yet. On the whole tile N46E008 (3601 × 3601 cells, 3,924
waves a step), over three runs of `srtm_gpu`, the GPU step gives the CPU
step's bed and loads on every cell, and the same mass off the map, but
takes 33 to 57 s a step against 0.5 s on the CPU. On the 256 × 256 crop
(2,874 waves) it is 1.1 s against 0.18 s.

The time is in the waves, not the kernel. Each wave is its own run of the
shim: it wraps about nine tile-sized buffers, which maps their pages into
the GPU's address space, then commits one command buffer and waits for it,
about 8 to 15 ms a wave against 0.13 ms on the CPU. The step pays off once
its waves share one set of wrapped buffers and one command buffer, with the
commit pass on the GPU too; that is the next step of ADR 0068.

## What is proved, and what is checked

| Claim | Where |
| --- | --- |
| When every wave returns `Ok`, the GPU step is settled and linked, and sends the outlets' sum off the map | `pull_step_on_gpu` |
| So it is the sequential step, cell for cell | `same_step` in [pull.pia.md](pull.pia.md), whose premises these are |
| Each thread writes only its own slots | the ownership check of ADR 0060 |
| A thread computes each cell's inflow, bed and load as the specification says | `gather`, `bed_after`, `load_after`, in the spread's `ensures` |
| Every index is in bounds and nothing overflows | every function |
| The toolchain from SPIR-V to Metal keeps the kernel's meaning | `srtm_gpu`, a differential test against `pull_step` (ADR 0068, section 6) |
