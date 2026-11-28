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

Every iteration reaches the same collectives in the same order, because
the loop over the waves runs over a range every iteration shares; piac
checks that before it proves anything. Within a wave, a cell does its work
only when the wave is its own, so that condition may depend on the
iteration: it holds no collective. Each iteration writes only the cells of
`bed`, `flux` and `seen` that it owns, `order.[q]` for iteration `q`,
which `@owns` with `pos` says ([ADR 0060](adr/0060-spread-v0-ownership-and-runtime.md)).

What is proved is that the step is race free, in bounds and free of
overflow, and that it leaves the same bed and loads as the sequential
step, cell for cell, and sends the same mass off the map. The proof goes
through a specification of the step as a function of its input (section
3): the loop over the waves keeps, as its invariant, that every cell of an
earlier wave holds that function's value, and every iteration learns the
others' invariant at each collective ([ADR
0088](adr/0088-shared-loop-invariants.md)). Then the step keeps the
promise pull.pia.md's theorem turns into equality with the sequential step
(section 6). `examples/streams/streams_test.c` also runs it against the
pull step.

```pia
module PullSpread : PullSpreadStep

import Pull.PullWaves as P
import Pia.Par.Collectives

interface PullSpreadStep @abi(c) = sig
  let pull_step_spread : (fill : [u16]) -> (down : [usize]) -> (acc : [u32]) -> (order : [usize])
      -> (pos : [usize]) -> (w : usize) -> (bed0 : [u32])
      -> (bed : borrowed inout mutable [u32]) -> (flux : borrowed inout mutable [u32])
      -> (seen : borrowed inout mutable [u64]) -> (gathered : borrowed inout mutable [u64])
      -> (wave : borrowed inout mutable [u32]) -> u64
    requires len down = len fill && len acc = len fill && len order = len fill && len pos = len fill && len bed0 = len fill
    requires len bed = len fill && len flux = len fill && len seen = len fill && len gathered = len fill && len wave = len fill
    requires w >= 3 && w < max usize && len fill < max u32
    requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
    requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
    requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
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

## 3. The step as a function

A cell's load depends only on its upstream neighbours' loads, and they
come before it in the height order, so the whole step is a function of the
input: `sflux` is the load leaving a cell, by recursion along the order,
and `sin` and `sbed` are its inflow and bed. The page proves that the
spread leaves exactly these in every cell. `good` collects the facts about
the order that the recursion needs to end. It is opaque, and the lemmas after it give
the facts one at a time.

```pia
let spec good (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) : bool @opaque
= len down = len fill && len order = len fill && len pos = len fill && len fill < max u32
  && (forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r)
  && (forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k)
  && (forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]])
  && (forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k]))
```

What `good` says: at a position, at a cell, about a cell's neighbour
downstream, about two positions, and about the lengths.

```pia
let lemma at_pos (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) (q : usize) : unit
  requires good fill down order pos && q < len fill
  ensures order.[q] < len fill && pos.[order.[q]] = q
  with good
= ()

let lemma at_cell (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) (k : usize) : unit
  requires good fill down order pos && k < len fill
  ensures pos.[k] < len fill && order.[pos.[k]] = k
  with good
= ()

let lemma drains (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) (k : usize) : unit
  requires good fill down order pos && k < len fill
  ensures down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  with good
= ()

let lemma sorted_at (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) (a : usize) (b : usize) : unit
  requires good fill down order pos && a < b && b < len fill
  ensures fill.[order.[b]] <= fill.[order.[a]]
  with good
= ()

let lemma orders_in (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) : unit
  requires good fill down order pos
  ensures forall (r in 0 .. len order). order.[r] < len fill
  with good
= ()

let lemma facts (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) : unit
  requires good fill down order pos
  ensures len down = len fill && len order = len fill && len pos = len fill && len fill < max u32
  with good
= ()

let lemma unpack (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) : unit
  requires good fill down order pos
  ensures forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  ensures forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  ensures forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  ensures forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  with good
= ()
```

The load leaving `c`: what erosion and deposition make of the loads its
upstream neighbours send it, or 0 where the sum does not fit, as the step
writes. A spec function may call only itself, so the eight terms are
written out. Opaque: only the lemmas below see its body.

```pia
let spec sflux (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (c : usize) : u64 @opaque
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && c < len fill && w >= 3 && w < max usize
  ensures result <= max u32
  decreases pos.[c]
  with good
= let g : u64 =
  ((((let nb0 = P.nbr (len down) w c 0 in
     if nb0 < len down then (if nb0 <> c && down.[nb0] = c then sflux fill down acc order pos w bed0 nb0 else 0) else 0)
    + (let nb1 = P.nbr (len down) w c 1 in
     if nb1 < len down then (if nb1 <> c && down.[nb1] = c then sflux fill down acc order pos w bed0 nb1 else 0) else 0))
   + ((let nb2 = P.nbr (len down) w c 2 in
     if nb2 < len down then (if nb2 <> c && down.[nb2] = c then sflux fill down acc order pos w bed0 nb2 else 0) else 0)
    + (let nb3 = P.nbr (len down) w c 3 in
     if nb3 < len down then (if nb3 <> c && down.[nb3] = c then sflux fill down acc order pos w bed0 nb3 else 0) else 0)))
  + (((let nb4 = P.nbr (len down) w c 4 in
     if nb4 < len down then (if nb4 <> c && down.[nb4] = c then sflux fill down acc order pos w bed0 nb4 else 0) else 0)
    + (let nb5 = P.nbr (len down) w c 5 in
     if nb5 < len down then (if nb5 <> c && down.[nb5] = c then sflux fill down acc order pos w bed0 nb5 else 0) else 0))
   + ((let nb6 = P.nbr (len down) w c 6 in
     if nb6 < len down then (if nb6 <> c && down.[nb6] = c then sflux fill down acc order pos w bed0 nb6 else 0) else 0)
    + (let nb7 = P.nbr (len down) w c 7 in
     if nb7 < len down then (if nb7 <> c && down.[nb7] = c then sflux fill down acc order pos w bed0 nb7 else 0) else 0)))) in
  if g + bed0.[c] <= max u32 then P.el g (P.cap_of fill down acc c) (bed0.[c]) else 0
```

What neighbour `d` of `c` sends it, and the sum of all eight, in the shape
of `P.inflow_of`.

```pia
let spec sterm (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (c : usize) (d : int{0..7}) : u64 @opaque
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && c < len fill && w >= 3 && w < max usize
  ensures result <= max u32
= let nb = P.nbr (len down) w c d in
  if nb < len down && nb < len fill then (if nb <> c && down.[nb] = c then sflux fill down acc order pos w bed0 nb else 0) else 0

let spec sin (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (c : usize) : u64 @opaque
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && c < len fill && w >= 3 && w < max usize
  ensures result <= 34'359'738'360
= ((sterm fill down acc order pos w bed0 c 0 + sterm fill down acc order pos w bed0 c 1) + (sterm fill down acc order pos w bed0 c 2 + sterm fill down acc order pos w bed0 c 3))
  + ((sterm fill down acc order pos w bed0 c 4 + sterm fill down acc order pos w bed0 c 5) + (sterm fill down acc order pos w bed0 c 6 + sterm fill down acc order pos w bed0 c 7))

let spec sbed (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (c : usize) : u64
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && c < len fill && w >= 3 && w < max usize
= let g = sin fill down acc order pos w bed0 c in
  if g + bed0.[c] <= max u32 then P.eb g (P.cap_of fill down acc c) (bed0.[c]) else bed0.[c]
```

`sflux`, unfolded once.

```pia
let lemma unfold (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (c : usize) : unit
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && c < len fill && w >= 3 && w < max usize
  ensures sflux fill down acc order pos w bed0 c = (if sin fill down acc order pos w bed0 c + bed0.[c] <= max u32 then P.el (sin fill down acc order pos w bed0 c) (P.cap_of fill down acc c) (bed0.[c]) else 0)
  with sflux, sin, sterm
= facts fill down order pos
```

A direction's term, where the neighbour's cell of `flux` holds its load if
it drains into `c`.

```pia
let lemma term_is (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (flux : [u32]) (c : usize) (d : int{0..7}) : unit
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && c < len fill && w >= 3 && w < max usize
  requires len flux = len fill
  requires (let nb = P.nbr (len down) w c d in
            nb < len down && nb < len fill && nb <> c && down.[nb] = c ==> flux.[nb] = sflux fill down acc order pos w bed0 nb)
  ensures P.from down flux w c d = sterm fill down acc order pos w bed0 c d
  with P.from, sterm
= facts fill down order pos
```

All eight terms make the inflow.

```pia
let lemma inflow_is (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (flux : [u32]) (c : usize) : unit
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && c < len fill && w >= 3 && w < max usize
  requires len flux = len fill
  requires P.from down flux w c 0 = sterm fill down acc order pos w bed0 c 0 && P.from down flux w c 1 = sterm fill down acc order pos w bed0 c 1
  requires P.from down flux w c 2 = sterm fill down acc order pos w bed0 c 2 && P.from down flux w c 3 = sterm fill down acc order pos w bed0 c 3
  requires P.from down flux w c 4 = sterm fill down acc order pos w bed0 c 4 && P.from down flux w c 5 = sterm fill down acc order pos w bed0 c 5
  requires P.from down flux w c 6 = sterm fill down acc order pos w bed0 c 6 && P.from down flux w c 7 = sterm fill down acc order pos w bed0 c 7
  ensures P.inflow_of down flux w c = sin fill down acc order pos w bed0 c
  with P.inflow_of, sin
= ()
```

## 4. The waves

The wave of each position of the height order: positions of equal height
share one, and the waves count up from the highest. It returns how many
there are. Of two positions, the earlier one of greater height has the
smaller wave (`waves_ok`, opaque).

```pia
let spec waves_ok (fill : [u16]) (order : [usize]) (wave : [u32]) : bool @opaque
  requires len order = len fill && len wave = len fill
  requires forall (r in 0 .. len order). order.[r] < len fill
= forall (a in 0 .. len fill) (b in 0 .. len fill).
    a < b && fill.[order.[a]] <> fill.[order.[b]] ==> wave.[a] < wave.[b]

let number_waves (fill : [u16]) (order : [usize]) (wave : borrowed inout mutable [u32]) : u32
  requires len order = len fill && len wave = len fill && len fill < max u32
  requires forall (r in 0 .. len order). order.[r] < len fill
  ensures forall (q in 0 .. len fill). wave.[q] < result
  ensures waves_ok fill order wave
  with waves_ok
= if len fill = 0 then 0
  else (
    let k : mutable u32 = 0 in
    wave.[0] <- 0;
    for q in 1 .. len fill
      invariant k < q && wave.[q - 1] = k
      invariant forall (r in 0 .. q). wave.[r] <= k
      invariant forall (a in 0 .. q) (b in 0 .. q).
        a < b && fill.[order.[a]] <> fill.[order.[b]] ==> wave.[a] < wave.[b]
    do
      if fill.[order.[q]] <> fill.[order.[q - 1]] then k <- k + 1 else ();
      wave.[q] <- k
    done;
    k + 1)
```

An upstream neighbour is in an earlier wave: it is higher, so it comes
before.

```pia
let lemma earlier (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) (wave : [u32]) (k : usize) (c : usize) : unit
  requires good fill down order pos && len wave = len fill && k < len fill && c < len fill
  requires len order = len fill && (forall (r in 0 .. len order). order.[r] < len fill) && waves_ok fill order wave
  requires k <> c && down.[k] = c
  ensures wave.[pos.[k]] < wave.[pos.[c]]
  with waves_ok
= facts fill down order pos;
  at_cell fill down order pos k;
  at_cell fill down order pos c;
  drains fill down order pos k;
  let a = pos.[k] in
  let b = pos.[c] in
  if b < a then sorted_at fill down order pos b a else ()
```

So after the exchange, in the wave of `c`, each of its upstream
neighbours holds its load, which is all a direction's term needs.

```pia
let lemma dir_done (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) (wave : [u32]) (t : u32) (c : usize) (d : int{0..7}) : unit
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && c < len fill && w >= 3 && w < max usize
  requires len bed = len fill && len flux = len fill && len seen = len fill && len wave = len fill
  requires len order = len fill && (forall (r in 0 .. len order). order.[r] < len fill) && waves_ok fill order wave
  requires wave.[pos.[c]] = t
  requires forall (q in 0 .. len fill). wave.[q] < t ==> flux.[order.[q]] = sflux fill down acc order pos w bed0 (order.[q])
    && bed.[order.[q]] = sbed fill down acc order pos w bed0 (order.[q]) && seen.[order.[q]] = sin fill down acc order pos w bed0 (order.[q])
  ensures P.from down flux w c d = sterm fill down acc order pos w bed0 c d
=
  facts fill down order pos;
  let nb = P.nbr (len down) w c d in
  if nb < len down && nb <> c && down.[nb] = c then (
    earlier fill down order pos wave nb c;
    at_cell fill down order pos nb;
    let r = pos.[nb] in
    assert wave.[r] < t;
    assert flux.[order.[r]] = sflux fill down acc order pos w bed0 (order.[r]);
    assert flux.[nb] = sflux fill down acc order pos w bed0 nb
  ) else ();
  term_is fill down acc order pos w bed0 flux c d
```

## 5. The step

One spread over the positions of the height order. Iteration `q` is cell
`order.[q]`. For each wave `t`, every iteration joins `exchange flux`,
then the cells of wave `t` pull their inflow into their own slot of
`gathered`; every iteration joins `exchange gathered`, and the cells of
wave `t` erode or deposit, writing their own cells of `bed`, `flux` and
`seen`.

The loop's invariant says that a cell of an earlier wave holds what the
step as a function says. It is about the iteration's own cells, and at
each collective in the loop every iteration learns every other's
([ADR 0088](adr/0088-shared-loop-invariants.md)). So after `exchange flux`
a cell knows that its upstream neighbours, which are in earlier waves,
hold their loads, and so that the inflow it gathers is `sin`.

```pia
let step_spread (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (bed : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32]) (seen : borrowed inout mutable [u64])
    (gathered : borrowed inout mutable [u64]) (wave : borrowed inout mutable [u32]) : unit
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && w >= 3 && w < max usize
  requires len bed = len fill && len flux = len fill && len seen = len fill && len gathered = len fill && len wave = len fill
  requires forall (k in 0 .. len down). down.[k] < len fill
  ensures forall (q in 0 .. len fill). flux.[order.[q]] = sflux fill down acc order pos w bed0 (order.[q])
    && bed.[order.[q]] = sbed fill down acc order pos w bed0 (order.[q]) && seen.[order.[q]] = sin fill down acc order pos w bed0 (order.[q])
=
  facts fill down order pos;
  orders_in fill down order pos;
  let waves = number_waves fill order wave in
  let n = len fill in
  spread q in 0 .. n @owns(bed, pos) @owns(flux, pos) @owns(seen, pos)
    ensures flux.[order.[q]] = sflux fill down acc order pos w bed0 (order.[q])
      && bed.[order.[q]] = sbed fill down acc order pos w bed0 (order.[q]) && seen.[order.[q]] = sin fill down acc order pos w bed0 (order.[q])
  do
    at_pos fill down order pos q;
    for t in 0 .. waves
      invariant wave.[q] < t ==> flux.[order.[q]] = sflux fill down acc order pos w bed0 (order.[q])
        && bed.[order.[q]] = sbed fill down acc order pos w bed0 (order.[q]) && seen.[order.[q]] = sin fill down acc order pos w bed0 (order.[q])
    do
      Pia.Par.exchange flux;
      let c = order.[q] in
      at_pos fill down order pos q;
      if wave.[q] = t then (
        dir_done fill down acc order pos w bed0 bed flux seen wave t c 0; dir_done fill down acc order pos w bed0 bed flux seen wave t c 1;
        dir_done fill down acc order pos w bed0 bed flux seen wave t c 2; dir_done fill down acc order pos w bed0 bed flux seen wave t c 3;
        dir_done fill down acc order pos w bed0 bed flux seen wave t c 4; dir_done fill down acc order pos w bed0 bed flux seen wave t c 5;
        dir_done fill down acc order pos w bed0 bed flux seen wave t c 6; dir_done fill down acc order pos w bed0 bed flux seen wave t c 7;
        inflow_is fill down acc order pos w bed0 flux c;
        gathered.[q] <- gather down flux w c
      ) else gathered.[q] <- 0;
      Pia.Par.exchange gathered;
      let c2 = order.[q] in
      at_pos fill down order pos q;
      if wave.[q] = t then (
        drains fill down order pos c2;
        let g = gathered.[q] in
        let b = bed0.[c2] in
        let d = down.[c2] in
        let drop : u16 = if d = c2 then 0 else fill.[c2] - fill.[d] in
        let cap = capacity_of acc.[c2] drop in
        unfold fill down acc order pos w bed0 c2;
        seen.[c2] <- g;
        if g + b <= max u32 then (
          bed.[c2] <- bed_after g cap b;
          flux.[c2] <- load_after g cap b
        ) else (
          bed.[c2] <- b;
          flux.[c2] <- 0
        )
      ) else ()
    done;
    at_pos fill down order pos q;
    assert wave.[q] < waves
  done
```

Every cell then holds what the function says, so the step keeps
pull.pia.md's promise: each cell's bed and load are what erosion and
deposition make of the inflow it took (`settled_if`), and that inflow is
what its upstream neighbours sent (`linked`).

```pia
let spec done_cell (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) (k : usize) : bool @opaque
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && k < len fill && w >= 3 && w < max usize
  requires len bed = len fill && len flux = len fill && len seen = len fill
= flux.[k] = sflux fill down acc order pos w bed0 k && bed.[k] = sbed fill down acc order pos w bed0 k && seen.[k] = sin fill down acc order pos w bed0 k

let spec cell_good (fill : [u16]) (down : [usize]) (acc : [u32]) (w : usize) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) (c : usize) : bool @opaque
  requires len down = len fill && len acc = len fill && len bed0 = len fill && c < len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
= P.holds_if fill down acc bed0 bed flux seen c && seen.[c] = P.inflow_of down flux w c

let lemma done_at (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) (k : usize) : unit
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && k < len fill && w >= 3 && w < max usize
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires done_cell fill down acc order pos w bed0 bed flux seen k
  ensures flux.[k] = sflux fill down acc order pos w bed0 k && bed.[k] = sbed fill down acc order pos w bed0 k && seen.[k] = sin fill down acc order pos w bed0 k
  with done_cell
= ()

let lemma term_from (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) (c : usize) (d : int{0..7}) : unit
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && c < len fill && w >= 3 && w < max usize
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires forall (k in 0 .. len fill). done_cell fill down acc order pos w bed0 bed flux seen k
  ensures P.from down flux w c d = sterm fill down acc order pos w bed0 c d
= let nb = P.nbr (len down) w c d in
  if nb < len down && nb < len fill then done_at fill down acc order pos w bed0 bed flux seen nb else ();
  term_is fill down acc order pos w bed0 flux c d

let lemma cell_ok (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) (c : usize) : unit
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && c < len fill && w >= 3 && w < max usize
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires forall (k in 0 .. len fill). done_cell fill down acc order pos w bed0 bed flux seen k
  ensures cell_good fill down acc w bed0 bed flux seen c
  with cell_good
=
  facts fill down order pos;
  done_at fill down acc order pos w bed0 bed flux seen c;
  unfold fill down acc order pos w bed0 c;
  term_from fill down acc order pos w bed0 bed flux seen c 0; term_from fill down acc order pos w bed0 bed flux seen c 1; term_from fill down acc order pos w bed0 bed flux seen c 2; term_from fill down acc order pos w bed0 bed flux seen c 3;
  term_from fill down acc order pos w bed0 bed flux seen c 4; term_from fill down acc order pos w bed0 bed flux seen c 5; term_from fill down acc order pos w bed0 bed flux seen c 6; term_from fill down acc order pos w bed0 bed flux seen c 7;
  inflow_is fill down acc order pos w bed0 flux c

let lemma cells_upto (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) (p : usize) : unit
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && p <= len fill && w >= 3 && w < max usize
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires forall (k in 0 .. len fill). done_cell fill down acc order pos w bed0 bed flux seen k
  ensures forall (c in 0 .. p). cell_good fill down acc w bed0 bed flux seen c
  decreases p
= if p > 0 then (
    cells_upto fill down acc order pos w bed0 bed flux seen (p - 1);
    cell_ok fill down acc order pos w bed0 bed flux seen (p - 1)
  ) else ()

let lemma settled_from (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) : unit
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && w >= 3 && w < max usize
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires forall (k in 0 .. len fill). done_cell fill down acc order pos w bed0 bed flux seen k
  ensures P.settled_if fill down acc bed0 bed flux seen
  ensures P.linked down flux seen w
  with P.settled_if, P.linked, cell_good
= facts fill down order pos;
  cells_upto fill down acc order pos w bed0 bed flux seen (len fill)
```

What leaves the map, added up along the order.

```pia
let outflow (order : [usize]) (down : [usize]) (flux : [u32]) : u64
  requires len down = len order && len flux = len order && len order < max u32
  requires forall (r in 0 .. len order). order.[r] < len down
  ensures result = P.osum order down flux (len order)
= let g : mutable u64 = 0 in
  for q in 0 .. len order
    invariant g = P.osum order down flux q
  do
    P.osum_next order down flux q;
    let c = order.[q] in
    g <- g + (if down.[c] = c then flux.[c] else 0)
  done;
  g
```

The interface's facts are `good`, and a fact at every position is one at
every cell.

```pia
let lemma make_good (fill : [u16]) (down : [usize]) (order : [usize]) (pos : [usize]) : unit
  requires len down = len fill && len order = len fill && len pos = len fill && len fill < max u32
  requires forall (r in 0 .. len order). order.[r] < len pos && pos.[order.[r]] = r
  requires forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
  requires forall (a in 0 .. len order) (b in 0 .. len order). a < b ==> fill.[order.[b]] <= fill.[order.[a]]
  requires forall (k in 0 .. len down). down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  ensures good fill down order pos
  with good
= ()

let lemma packed (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) : unit
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && w >= 3 && w < max usize
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires forall (q in 0 .. len fill). order.[q] < len fill
  requires forall (q in 0 .. len fill). flux.[order.[q]] = sflux fill down acc order pos w bed0 (order.[q])
    && bed.[order.[q]] = sbed fill down acc order pos w bed0 (order.[q]) && seen.[order.[q]] = sin fill down acc order pos w bed0 (order.[q])
  ensures forall (q in 0 .. len fill). done_cell fill down acc order pos w bed0 bed flux seen (order.[q])
  with done_cell
= ()

let lemma by_cell_upto (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32]) (bed : [u32]) (flux : [u32]) (seen : [u64]) (p : usize) : unit
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && p <= len fill && w >= 3 && w < max usize
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires forall (q in 0 .. len fill). done_cell fill down acc order pos w bed0 bed flux seen (order.[q])
  ensures forall (k in 0 .. p). done_cell fill down acc order pos w bed0 bed flux seen k
  decreases p
= if p > 0 then (
    by_cell_upto fill down acc order pos w bed0 bed flux seen (p - 1);
    facts fill down order pos;
    at_cell fill down order pos (p - 1);
    let r = pos.[p - 1] in
    assert done_cell fill down acc order pos w bed0 bed flux seen (order.[r])
  ) else ()
```

The C entry point: the step, then what it sent off the map.

```pia
let pull_step_spread (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (bed : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32]) (seen : borrowed inout mutable [u64])
    (gathered : borrowed inout mutable [u64]) (wave : borrowed inout mutable [u32]) : u64
=
  make_good fill down order pos;
  step_spread fill down acc order pos w bed0 bed flux seen gathered wave;
  facts fill down order pos;
  orders_in fill down order pos;
  packed fill down acc order pos w bed0 bed flux seen;
  by_cell_upto fill down acc order pos w bed0 bed flux seen (len fill);
  settled_from fill down acc order pos w bed0 bed flux seen;
  outflow order down flux
```

## 6. The same step as the sequential one

The theorem, from pull.pia.md: a step that keeps this promise leaves the
same bed and loads as the sequential step, cell for cell, and sends the
same mass off the map. So does this one.

```pia
let lemma same_as_sequential (fill : [u16]) (down : [usize]) (acc : [u32]) (order : [usize]) (pos : [usize]) (w : usize) (bed0 : [u32])
    (ba : [u32]) (fa : [u32]) (sa : [u64]) (ga : u64) (bed : [u32]) (flux : [u32]) (seen : [u64]) : unit
  requires good fill down order pos && len acc = len fill && len bed0 = len fill && w >= 3 && w < max usize
  requires len down = len fill && len order = len fill && len pos = len fill && len fill < max u32
  requires len ba = len fill && len fa = len fill && len sa = len fill
  requires len bed = len fill && len flux = len fill && len seen = len fill
  requires forall (k in 0 .. len down). down.[k] < len fill
  requires P.settled fill down acc bed0 ba fa sa && P.linked down fa sa w
  requires ga = P.osum order down fa (len fill)
  requires P.settled_if fill down acc bed0 bed flux seen && P.linked down flux seen w
  ensures forall (k in 0 .. len fill). ba.[k] = bed.[k] && fa.[k] = flux.[k]
  ensures ga = P.osum order down flux (len fill)
= unpack fill down order pos;
  P.same_step fill down acc order pos w bed0 ba fa sa ga bed flux seen (P.osum order down flux (len fill)) 0
```

## What is proved

| Claim | Where |
| --- | --- |
| Every iteration reaches the same collectives in the same order | piac's protocol check, before any goal |
| No iteration writes a cell another iteration reads or writes | `@owns(bed, pos)`, `@owns(flux, pos)`, `@owns(seen, pos)`, and the exchanges that publish `flux` and `gathered` |
| Every cell holds the step's function of the input: its load, bed and inflow | `step_spread`, through the shared loop invariant |
| The step keeps pull.pia.md's promise, settled and linked | `settled_from` |
| It leaves the same bed and loads as the sequential step, and sends the same mass off the map | `same_as_sequential`, with pull.pia.md's `same_step` |
| No index is out of bounds and no sum overflows | every goal of the page |
