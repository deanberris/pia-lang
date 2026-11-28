# Demo: the sediment step in one spread, with collectives

The [pull step](pull.pia.md) takes the cells in *waves*, one for each
height, highest first. Each wave is a `spread`, and a short pass then
commits it in order. That is a fork and a join for every wave, written as
a host loop around the spreads.

This page writes the same step as **one** `spread` over the cells, which
loops over the waves itself and uses collectives
([ADR 0086](adr/0086-spread-collectives.md)) where the waves meet:

- `exchange flux` publishes the loads every earlier wave has sent, so a
  cell can read its neighbours' cells of `flux`, which other iterations
  own and write.
- `exchange gathered` ends that window, so the cells of this wave may
  write `flux` again.
- `sum` adds up the load leaving the map at the outlets, every
  iteration's contribution at once.

Every iteration reaches the same collectives in the same order, because
the loop over the waves runs over a range every iteration shares; piac
checks that before it proves anything. Within a wave, a cell does its work
only when the wave is its own, so that condition may depend on the
iteration: it holds no collective. Each iteration writes only the cells of
`bed` and `flux` that it owns, `order.[q]` for iteration `q`, which
`@owns` with `pos` says ([ADR 0060](adr/0060-spread-v0-ownership-and-runtime.md)).

What is proved here is that the step is race free, in bounds and free of
overflow, and that every cell computes its inflow, bed and load as
pull.pia.md's specification says, through the interface `PullWaves` that
page provides. That the waves, taken in this order, give the sequential
step is pull.pia.md's theorem; that this step gives the same cells as the
pull step is checked by running both, in `examples/streams/streams_test.c`.

```pia
module PullSpread : PullSpreadStep

import Pull.PullWaves as P
import Pia.Par.Collectives

interface PullSpreadStep @abi(c) = sig
  let pull_step_spread : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (order : [usize])
      -> (pos : [usize]) -> (w : usize) -> (bed0 : [u32])
      -> (bed : borrowed inout mutable [u32]) -> (flux : borrowed inout mutable [u32])
      -> (gathered : borrowed inout mutable [u64]) -> (wave : borrowed inout mutable [u32]) -> u64
    requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
    requires len bed = len fill && len flux = len fill && len gathered = len fill && len wave = len fill
    requires w >= 3 && w < max usize && len fill < max u32
    requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
    requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
    requires forall (k in 0 .. len down). down.[k] < len fill
end
```

## 1. One cell's inflow

These are pull.pia.md's, as pull_gpu.pia.md has them: the neighbour in a
direction, the load it sends, and the sum of all eight. `gather` takes
`flux`, which the spread writes, so the spread may call it only while a
collective has published `flux`: then no iteration writes it, and every
iteration may read all of it.

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

## 2. Erosion and deposition

The capacity of a cell, from its flow and its drop, and the bed and load
it is left with, each as the specification says.

```pia
let capacity_of (a : u32) (drop : u16) : u32
  ensures result = P.cap_rule a drop
=
  let d : u32 = drop in
  let c : u64 = (a >> 4) + (d << 2) in
  if c < max u16 then c else max u16

let bed_after (i : u64) (cap : u32) (bed : u32) : u32
  requires i + bed <= max u32
  ensures result = P.eb i cap bed
= if i < cap then (let room = cap - i in if room < bed then bed - room else 0)
  else bed + (i - cap)

let load_after (i : u64) (cap : u32) (bed : u32) : u32
  requires i + bed <= max u32
  ensures result = P.el i cap bed
= if i < cap then (let room = cap - i in if room < bed then cap else i + bed)
  else cap
```

## 3. The waves

The wave of each position of the height order: positions of equal height
share one, and the waves count up from the highest. It returns how many
there are.

```pia
let number_waves (fill : [u16]) (order : [usize]) (wave : borrowed inout mutable [u32]) : u32
  requires len order = len fill && len wave = len fill && len fill < max u32
  requires forall (r in 0 .. len order). order.[r] < len fill
= if len fill = 0 then 0
  else (
    let k : mutable u32 = 0 in
    wave.[0] <- 0;
    for q in 1 .. len fill
      invariant k < q
    do
      if fill.[order.[q]] <> fill.[order.[q - 1]] then k <- k + 1 else ();
      wave.[q] <- k
    done;
    k + 1)
```

## 4. The step

One spread over the positions of the height order. Iteration `q` is cell
`order.[q]`. For each wave `t`, every iteration joins `exchange flux`,
then the cells of wave `t` pull their inflow into their own slot of
`gathered`; every iteration joins `exchange gathered`, and the cells of
wave `t` erode or deposit, writing their own cells of `bed` and `flux`. A
cell's upstream neighbours are strictly higher, so they are in earlier
waves, and the loads they sent were written before the exchange that
published them. At the end, `sum` adds up what the outlets send off the
map, and the step returns it.

```pia
let pull_step_spread (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (bed : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32])
    (gathered : borrowed inout mutable [u64]) (wave : borrowed inout mutable [u32]) : u64
=
  let waves = number_waves fill order wave in
  let n = len fill in
  spread q in 0 .. n @owns(bed, pos) @owns(flux, pos) do
    for t in 0 .. waves do
      Pia.Par.exchange flux;
      let c = order.[q] in
      gathered.[q] <- (if wave.[q] = t then gather down flux w c else 0);
      Pia.Par.exchange gathered;
      let c2 = order.[q] in
      if wave.[q] = t then (
        let g = gathered.[q] in
        let b = bed0.[c2] in
        let d = down.[c2] in
        let drop : u16 = if d = c2 then 0 else fill.[c2] - fill.[d] in
        let cap = capacity_of acc.[c2] drop in
        if g + b <= max u32 then (
          bed.[c2] <- bed_after g cap b;
          flux.[c2] <- load_after g cap b
        ) else (
          bed.[c2] <- b;
          flux.[c2] <- 0
        )
      ) else ()
    done;
    Pia.Par.exchange flux;
    let c3 = order.[q] in
    gathered.[q] <- Pia.Par.sum (if down.[c3] = c3 then flux.[c3] else 0)
  done;
  if n > 0 then gathered.[0] else 0
```

## What is proved

| Claim | Where |
| --- | --- |
| Every iteration reaches the same collectives in the same order | piac's protocol check, before any goal |
| No iteration writes a cell another iteration reads or writes | `@owns(bed, pos)`, `@owns(flux, pos)`, and the exchanges that publish `flux` and `gathered` |
| Each cell computes its inflow, bed and load as the specification says | `gather`, `bed_after`, `load_after`, `capacity_of` |
| No index is out of bounds and no sum overflows | every goal of the page |
| The step leaves the same cells as the pull step | run, not proved: `examples/streams/streams_test.c` |
