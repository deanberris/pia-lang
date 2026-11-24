# Demo: sediment transport by basin, in parallel

Cells in different basins never exchange sediment: water runs downhill
from a cell to the cell below it, and a cell and the cell it drains to
have the same watershed ([sediment.pia.md](sediment.pia.md), section 7).
So every basin can run its time steps on its own core. This page is that
version of sediment transport, a `spread` over the basins
([ADR 0060](adr/0060-spread-v0-ownership-and-runtime.md)), with the
conservation law proved for each basin and summed over all of them:

```text
sum bed + sum load + sum inflow + sum gone_by = old (sum bed + sum load + sum inflow)
```

exactly, where `gone_by.[b]` is what left the map through basin `b`'s
outlet. The page is its own module, so it proves in parallel with the
others; `main.c` calls it with the labels and the height order that
`drainage` computes, and checks that it gives the same result as the
sequential `sediment`, cell for cell.

```pia
module Basins : BasinTransport

interface BasinTransport @abi(c) = sig
  let sediment_basins : (fill : [u16]) -> (down : [usize]) -> (acc : [u32])
      -> (label : [usize]) -> (order : [usize]) -> (steps : u32)
      -> (bed : borrowed inout mutable [u32]) -> (load : out mutable [u32])
      -> (inflow : out mutable [u32]) -> (flux : out mutable [u32])
      -> (gone_by : out mutable [u32]) -> (border : out mutable [usize])
      -> (keys : out mutable [usize]) -> (place2 : out mutable [usize])
      -> (pos2 : out mutable [usize]) -> (cnt : out mutable [u32])
      -> (first : out mutable [usize]) -> (next : out mutable [usize])
      -> (last : out mutable [usize]) -> (gowner : out mutable [usize]) -> u64
    requires len down = len fill && len acc = len fill && len label = len fill && len order = len fill
    requires len bed = len fill && len load = len fill && len inflow = len fill && len flux = len fill && len gone_by = len fill
    requires len border = len fill && len keys = len fill && len place2 = len fill && len pos2 = len fill
    requires len cnt = len fill && len first = len fill && len next = len fill && len last = len fill && len gowner = len fill
    requires len fill >= 1 && len fill < max u32
    requires forall (k in 0..len down).
               down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
    requires forall (k in 0..len label). label.[at down k] = label.[k] && at label k < len fill
    requires forall (q in 0..len order). order.[q] < len fill
end
```

## 1. Sums, cells and steps

The pieces of [sediment.pia.md](sediment.pia.md) this page needs, copied
because a module cannot yet export lemmas over buffers
([#327](https://github.com/deanberris/pia-lang/issues/327)): the sum and
its point update, one cell's erosion or deposition, and the arithmetic
that chains them.

```pia
let spec elt (xs : [u32]) (i : usize) : u32
  requires i < len xs
= xs.[i]

let spec sum (xs : [u32]) (n : usize) : u64
  requires n <= len xs && n <= max u32 + 1
  ensures result <= (max u32 + 1) * n
  decreases n
= if n = 0 then 0 else sum xs (n - 1) + elt xs (n - 1)

let lemma step (xs : [u32]) (ys : [u32]) (n : usize) : unit
  requires 0 < n && n <= len xs && n <= len ys && n <= max u32 + 1
  requires sum ys (n - 1) = sum xs (n - 1) && ys.[n - 1] = xs.[n - 1]
  ensures sum ys n = sum xs n
= ()

let lemma step_after (xs : [u32]) (ys : [u32]) (i : usize) (n : usize) : unit
  requires i < n - 1 && n <= len xs && n <= len ys && n <= max u32 + 1
  requires sum ys (n - 1) + xs.[i] = sum xs (n - 1) + ys.[i] && ys.[n - 1] = xs.[n - 1]
  ensures sum ys n + xs.[i] = sum xs n + ys.[i]
= ()

let lemma step_at (xs : [u32]) (ys : [u32]) (i : usize) : unit
  requires i < len xs && i < len ys && i < max u32 + 1
  requires sum ys i = sum xs i
  ensures sum ys (i + 1) + xs.[i] = sum xs (i + 1) + ys.[i]
= ()

let lemma frame (xs : [u32]) (ys : [u32]) (i : usize) (n : usize) : unit
  requires len xs = len ys && n <= i && i < len xs && len xs <= max u32 + 1
  requires forall (k in 0 .. len xs). k <> i ==> ys.[k] = xs.[k]
  ensures sum ys n = sum xs n
  decreases n
= if n > 0 then (frame xs ys i (n - 1); assert ys.[n - 1] = xs.[n - 1]; step xs ys n)

let lemma update (xs : [u32]) (ys : [u32]) (i : usize) (n : usize) : unit
  requires len xs = len ys && i < n && n <= len xs && len xs <= max u32 + 1
  requires forall (k in 0 .. len xs). k <> i ==> ys.[k] = xs.[k]
  ensures sum ys n + xs.[i] = sum xs n + ys.[i]
  decreases n
= if n > i + 1 then (update xs ys i (n - 1); assert ys.[n - 1] = xs.[n - 1]; step_after xs ys i n)
  else (frame xs ys i i; step_at xs ys i; assert n = i + 1)

let lemma at_le (xs : [u32]) (i : usize) : unit
  requires i < len xs && i < max u32 + 1
  ensures xs.[i] <= sum xs (i + 1)
= ()

let lemma mono (xs : [u32]) (m : usize) (n : usize) : unit
  requires m <= n && n <= len xs && n <= max u32 + 1
  ensures sum xs m <= sum xs n
  decreases n
= if n > m then mono xs m (n - 1)

let lemma elt_le (xs : [u32]) (i : usize) (n : usize) : unit
  requires i < n && n <= len xs && n <= max u32 + 1
  ensures xs.[i] <= sum xs n
= at_le xs i; mono xs (i + 1) n

let lemma zero (xs : [u32]) (n : usize) : unit
  requires n <= len xs && n <= max u32 + 1
  requires forall (k in 0 .. n). xs.[k] = 0
  ensures sum xs n = 0
  decreases n
= if n > 0 then (zero xs (n - 1); assert xs.[n - 1] = 0)

let set (xs : borrowed inout mutable [u32]) (i : usize) (v : u32) : unit
  requires i < len xs && len xs <= max u32 + 1
  ensures xs.[i] = v
  ensures forall (k in 0 .. len xs). k <> i ==> xs.[k] = old (xs.[k])
  ensures sum xs (len xs) + old (xs.[i]) = sum (old xs) (len xs) + v
= let w = xs.[i] in
  xs.[i] <- v;
  update (old xs) xs i (len xs);
  assert w = old (xs.[i])

let spec at (xs : [usize]) (k : usize) : usize
  requires k < len xs
= xs.[k]

let cell = type { bed : u32; load : u32 }

let erode_or_deposit (inflow : u32) (capacity : u32) (bed : u32) : cell
  requires bed + inflow <= max u32
  ensures result.bed + result.load = bed + inflow
  ensures inflow < capacity ==> result.bed <= bed && inflow <= result.load && result.load <= capacity
  ensures capacity <= inflow ==> bed <= result.bed && result.load = capacity
= if inflow < capacity then
    (let room = capacity - inflow in
     let e = if room < bed then room else bed in
     { bed = bed - e; load = inflow + e })
  else { bed = bed + (inflow - capacity); load = capacity }

let lemma balance (a : u64) (b : u64) (c : u64) (a0 : u64) (b0 : u64) (c0 : u64) (d : u32) (i : u32) (rb : u32) (rl : u32) : unit
  requires a + d = a0 + rb && b = b0 + rl && c + i = c0 && rb + rl = d + i
  ensures a + b + c = a0 + b0 + c0
= ()

let lemma chain (b : u64) (l : u64) (i : u64) (g : u64) (b1 : u64) (l1 : u64) (i1 : u64) : unit
  requires b + l + i + g <= max u32 && b1 + l1 + i1 = b + l + i
  ensures b1 + l1 + i1 + g <= max u32
= ()

let capacity_of (a : u32) (drop : u16) : u32 =
  let d : u32 = drop in
  let c : u64 = (a >> 4) + (d << 2) in
  if c < max u16 then c else max u16

let total (xs : [u32]) : u64
  requires len xs <= max u32 + 1
  ensures result = sum xs (len xs)
=
  let t : mutable u64 = 0 in
  for i in 0 .. len xs
    invariant t = sum xs i
  do
    t <- t + xs.[i]
  done;
  t

let blank (order : out mutable [usize]) (v : usize) : unit
  ensures forall (q in 0 .. len order). order.[q] = v
= for q in 0 .. len order
    invariant forall (j in 0 .. q). order.[j] = v
  do order.[q] <- v done
```

## 2. The height order grouped by basin

To visit a basin's cells in height order without scanning the whole map,
the height order is grouped by basin: the same counting sort as
`height_order`'s, with the basin labels as keys and one bucket per cell
that can be an outlet, so that the places `first.[b]` up to `last.[b]` of
`border` are the cells of basin `b`, highest first.

How many of keys.[k ..] are h.

```pia
let spec kcount (keys : [usize]) (h : usize) (k : usize) : usize
  requires k <= len keys
  ensures result <= len keys - k
  decreases len keys - k
= if k = len keys then 0 else (if keys.[k] = h then 1 else 0) + kcount keys h (k + 1)
```

cnt.[h] is the number of keys equal to h, and cnt sums to n.

```pia
let ghistogram (keys : [usize]) (nb : usize) (cnt : out mutable [u32]) : unit
  requires len cnt = nb && nb >= 1 && nb <= max u32 && len keys <= max u32
  requires forall (k in 0 .. len keys). at keys k < nb
  ensures forall (h in 0 .. nb). cnt.[h] = kcount keys h 0
  ensures sum cnt nb = len keys
= for h in 0 .. nb
    invariant forall (j in 0 .. h). cnt.[j] = 0
  do cnt.[h] <- 0 done;
  zero cnt nb;
  for k in 0 .. len keys
    invariant sum cnt nb = k
    invariant forall (h in 0 .. nb). cnt.[h] + kcount keys h k = kcount keys h 0
  do
    let h : usize = keys.[k] in
    let c = cnt.[h] in
    elt_le cnt h nb;
    set cnt h (c + 1)
  done
```

Each key's bucket of places, the highest key first, stated by its
neighbour.

```pia
let goffsets (n : usize) (nb : usize) (cnt : [u32]) (first : out mutable [usize]) (next : out mutable [usize]) (last : out mutable [usize]) : unit
  requires len cnt = nb && len first = nb && len next = nb && len last = nb
  requires nb >= 1 && nb <= max u32 && sum cnt nb = n
  ensures last.[0] = n && first.[nb - 1] = 0
  ensures forall (h in 0 .. nb). next.[h] = first.[h] && first.[h] + cnt.[h] = last.[h] && last.[h] <= n
  ensures forall (h in 0 .. nb - 1). first.[h] = last.[h + 1]
= let acc : mutable u64 = 0 in
  for t in 0 .. nb
    invariant acc = sum cnt t && acc <= n
    invariant t > 0 ==> last.[0] = n
    invariant t > 0 ==> first.[t - 1] + acc = n
    invariant forall (h in 0 .. t). next.[h] = first.[h] && first.[h] + cnt.[h] = last.[h] && last.[h] <= n
    invariant forall (h in 0 .. t). h + 1 < t ==> first.[h] = last.[h + 1]
  do
    mono cnt (t + 1) nb;
    let c = cnt.[t] in
    last.[t] <- n - acc;
    acc <- acc + c;
    first.[t] <- n - acc;
    next.[t] <- n - acc
  done
```

Writes t into owner.[lo .. hi] and nothing else.

```pia
let gmark (owner : borrowed inout mutable [usize]) (lo : usize) (hi : usize) (t : usize) : unit
  requires lo <= hi && hi <= len owner
  ensures forall (j in 0 .. len owner). (lo <= j && j < hi ==> owner.[j] = t) && (j < lo || hi <= j ==> owner.[j] = old (owner.[j]))
= for q in lo .. hi
    invariant forall (j in 0 .. len owner). (lo <= j && j < q ==> owner.[j] = t) && (j < lo || q <= j ==> owner.[j] = old (owner.[j]))
  do
    owner.[q] <- t
  done
```

owner.[q] is the key whose bucket holds place q.

```pia
let gowners (n : usize) (nb : usize) (cnt : [u32]) (first : [usize]) (last : [usize]) (owner : out mutable [usize]) : unit
  requires len cnt = nb && len first = nb && len last = nb && len owner = n && nb >= 1
  requires last.[0] = n && first.[nb - 1] = 0
  requires forall (h in 0 .. nb). first.[h] + cnt.[h] = last.[h] && last.[h] <= n
  requires forall (h in 0 .. nb - 1). first.[h] = last.[h + 1]
  ensures forall (q in 0 .. n). at owner q < nb && first.[at owner q] <= q && q < last.[at owner q]
  ensures forall (h in 0 .. nb) (q in 0 .. n). first.[h] <= q && q < last.[h] ==> at owner q = h
  ensures forall (a in 0 .. n) (b in 0 .. n). a < b ==> at owner b <= at owner a
= let w : mutable usize = n in
  for t in 0 .. nb
    invariant w <= n
    invariant t < nb ==> w = last.[t]
    invariant t = nb ==> w = 0
    invariant forall (h in 0 .. t). w <= first.[h]
    invariant forall (q in w .. n). at owner q < t && first.[at owner q] <= q && q < last.[at owner q]
    invariant forall (h in 0 .. t) (q in w .. n). first.[h] <= q && q < last.[h] ==> owner.[q] = h
    invariant forall (a in w .. n) (b in w .. n). a < b ==> at owner b <= at owner a
  do
    let lo = first.[t] in
    assert lo + cnt.[t] = last.[t] && lo <= w;
        gmark owner lo w t;
    w <- lo;
    if t + 1 < nb then assert lo = last.[t + 1] else ()
  done
```

Each place gets the next key's index, in key order; a place q holds a key
equal to owner.[q].

```pia
let gplace (keys : [usize]) (nb : usize) (first : [usize]) (last : [usize]) (owner : [usize]) (next : borrowed inout mutable [usize]) (order : out mutable [usize]) (pos : out mutable [usize]) : unit
  requires len first = nb && len last = nb && len next = nb
  requires len owner = len keys && len order = len keys && len pos = len keys
  requires forall (h in 0 .. nb). next.[h] = first.[h] && first.[h] + kcount keys h 0 = last.[h] && last.[h] <= len keys
  requires forall (k in 0 .. len keys). at keys k < nb
  requires forall (q in 0 .. len keys). at owner q < nb && first.[at owner q] <= q && q < last.[at owner q]
  requires forall (h in 0 .. nb) (q in 0 .. len keys). first.[h] <= q && q < last.[h] ==> at owner q = h
  ensures forall (q in 0 .. len order). order.[q] < len pos && pos.[order.[q]] = q && keys.[order.[q]] = at owner q
  ensures forall (k in 0 .. len pos). pos.[k] < len order && order.[pos.[k]] = k
= blank order (len keys);
  assert (forall (q in 0 .. len keys). next.[at owner q] = first.[at owner q]);
  assert (forall (q in 0 .. len keys). next.[at owner q] <= q);
  for k in 0 .. len keys
    invariant forall (h in 0 .. nb). first.[h] <= next.[h] && next.[h] + kcount keys h k = last.[h]
    invariant forall (q in 0 .. len keys).
      (q < next.[at owner q] ==> order.[q] < k && pos.[order.[q]] = q && keys.[order.[q]] = at owner q)
      && (next.[at owner q] <= q ==> order.[q] = len keys)
    invariant forall (j in 0 .. k). pos.[j] < len keys && order.[pos.[j]] = j
  do
    let h : usize = keys.[k] in
    let p = next.[h] in
    assert kcount keys h k = 1 + kcount keys h (k + 1);
    assert p < last.[h] && last.[h] <= len keys;
    assert at owner p = h;
    order.[p] <- k;
    pos.[k] <- p;
    next.[h] <- p + 1
  done;
  assert (forall (h in 0 .. nb). next.[h] = last.[h]);
  assert (forall (q in 0 .. len keys). q < next.[at owner q])
```

The keys of the grouping: each place of the height order, labelled by its
cell's basin.

```pia
let basin_keys (label : [usize]) (order : [usize]) (keys : out mutable [usize]) : unit
  requires len order = len label && len keys = len label
  requires forall (q in 0 .. len order). order.[q] < len label
  requires forall (k in 0 .. len label). at label k < len label
  ensures forall (q in 0 .. len keys). keys.[q] = label.[order.[q]] && at keys q < len label
= for q in 0 .. len order
    invariant forall (j in 0 .. q). keys.[j] = label.[order.[j]] && at keys j < len label
  do
    keys.[q] <- label.[order.[q]]
  done
```

The cells grouped by basin, each basin's cells in the height order: the
places first.[b] up to last.[b] of `border` are basin b's cells.

```pia
let basin_order (label : [usize]) (order : [usize]) (border : out mutable [usize])
    (keys : out mutable [usize]) (place2 : out mutable [usize]) (pos2 : out mutable [usize])
    (cnt : out mutable [u32]) (first : out mutable [usize]) (next : out mutable [usize])
    (last : out mutable [usize]) (owner : out mutable [usize]) : unit
  requires len order = len label && len border = len label && len keys = len label
  requires len place2 = len label && len pos2 = len label && len owner = len label
  requires len cnt = len label && len first = len label && len next = len label && len last = len label
  requires len label >= 1 && len label <= max u32
  requires forall (q in 0 .. len order). order.[q] < len label
  requires forall (k in 0 .. len label). at label k < len label
  ensures forall (b in 0 .. len label). first.[b] <= last.[b] && last.[b] <= len label
  ensures forall (q in 0 .. len border). border.[q] < len label && label.[border.[q]] = at owner q
  ensures forall (b in 0 .. len label) (q in 0 .. len border). first.[b] <= q && q < last.[b] ==> at owner q = b
= let n = len label in
  basin_keys label order keys;
  ghistogram keys n cnt;
  goffsets n n cnt first next last;
  gowners n n cnt first last owner;
  gplace keys n first last owner next place2 pos2;
  for q in 0 .. n
    invariant forall (j in 0 .. q). border.[j] < n && label.[border.[j]] = at owner j
  do
    border.[q] <- order.[place2.[q]]
  done
```

## 3. A basin's sum

`bsum xs label b n` is the sum of basin `b`'s cells among the first `n`.
It says what it reads, the cells labelled `b`
([ADR 0060](adr/0060-spread-v0-ownership-and-runtime.md), section 3), so
a write in another basin leaves it alone, which is what lets a `spread`
over basins prove a law per basin. Its point update is proved like
`sum`'s, by induction through steps with no quantifier.

The sum of basin b's cells among xs.[0 .. n].

```pia
let spec bsum (xs : [u32]) (label : [usize]) (b : usize) (n : usize) : u64
  requires n <= len xs && len label = len xs && n <= max u32 + 1
  reads xs.[c] where label.[c] = b
  ensures result <= (max u32 + 1) * n
  decreases n
= if n = 0 then 0 else bsum xs label b (n - 1) + (if label.[n - 1] = b then elt xs (n - 1) else 0)
```

```pia
let lemma bstep (xs : [u32]) (ys : [u32]) (label : [usize]) (b : usize) (n : usize) : unit
  requires 0 < n && n <= len xs && len ys = len xs && len label = len xs && n <= max u32 + 1
  requires bsum ys label b (n - 1) = bsum xs label b (n - 1) && ys.[n - 1] = xs.[n - 1]
  ensures bsum ys label b n = bsum xs label b n
= ()
```

```pia
let lemma bstep_after (xs : [u32]) (ys : [u32]) (label : [usize]) (b : usize) (i : usize) (n : usize) : unit
  requires i < n - 1 && n <= len xs && len ys = len xs && len label = len xs && n <= max u32 + 1
  requires bsum ys label b (n - 1) + xs.[i] = bsum xs label b (n - 1) + ys.[i] && ys.[n - 1] = xs.[n - 1]
  ensures bsum ys label b n + xs.[i] = bsum xs label b n + ys.[i]
= ()
```

```pia
let lemma bstep_at (xs : [u32]) (ys : [u32]) (label : [usize]) (b : usize) (i : usize) : unit
  requires i < len xs && len ys = len xs && len label = len xs && i < max u32 + 1 && label.[i] = b
  requires bsum ys label b i = bsum xs label b i
  ensures bsum ys label b (i + 1) + xs.[i] = bsum xs label b (i + 1) + ys.[i]
= ()
```

```pia
let lemma bframe (xs : [u32]) (ys : [u32]) (label : [usize]) (b : usize) (i : usize) (n : usize) : unit
  requires len ys = len xs && len label = len xs && n <= i && i < len xs && len xs <= max u32 + 1
  requires forall (k in 0 .. len xs). k <> i ==> ys.[k] = xs.[k]
  ensures bsum ys label b n = bsum xs label b n
  decreases n
= if n > 0 then (bframe xs ys label b i (n - 1); assert ys.[n - 1] = xs.[n - 1]; bstep xs ys label b n)
```

The point update for a cell of basin b.

```pia
let lemma bupdate (xs : [u32]) (ys : [u32]) (label : [usize]) (b : usize) (i : usize) (n : usize) : unit
  requires len ys = len xs && len label = len xs && i < n && n <= len xs && len xs <= max u32 + 1
  requires label.[i] = b
  requires forall (k in 0 .. len xs). k <> i ==> ys.[k] = xs.[k]
  ensures bsum ys label b n + xs.[i] = bsum xs label b n + ys.[i]
  decreases n
= if n > i + 1 then (bupdate xs ys label b i (n - 1); assert ys.[n - 1] = xs.[n - 1]; bstep_after xs ys label b i n)
  else (bframe xs ys label b i i; bstep_at xs ys label b i; assert n = i + 1)
```

```pia
let lemma bat_le (xs : [u32]) (label : [usize]) (b : usize) (i : usize) : unit
  requires i < len xs && len label = len xs && i < max u32 + 1 && label.[i] = b
  ensures xs.[i] <= bsum xs label b (i + 1)
= ()
```

```pia
let lemma bmono (xs : [u32]) (label : [usize]) (b : usize) (m : usize) (n : usize) : unit
  requires m <= n && n <= len xs && len label = len xs && n <= max u32 + 1
  ensures bsum xs label b m <= bsum xs label b n
  decreases n
= if n > m then bmono xs label b m (n - 1)
```

A cell of basin b is at most the basin's sum.

```pia
let lemma belt_le (xs : [u32]) (label : [usize]) (b : usize) (i : usize) (n : usize) : unit
  requires i < n && n <= len xs && len label = len xs && n <= max u32 + 1 && label.[i] = b
  ensures xs.[i] <= bsum xs label b n
= bat_le xs label b i; bmono xs label b (i + 1) n
```

A write to a cell of basin b, whose contract is the point update for the
basin's sum; it touches only that cell.

```pia
let bset (xs : borrowed inout mutable [u32]) (label : [usize]) (b : usize) (i : usize) (v : u32) : unit @owns(xs, label, b)
  requires i < len xs && len label = len xs && len xs <= max u32 + 1 && label.[i] = b
  ensures xs.[i] = v
  ensures forall (k in 0 .. len xs). k <> i ==> xs.[k] = old (xs.[k])
  ensures bsum xs label b (len xs) + old (xs.[i]) = bsum (old xs) label b (len xs) + v
= let w = xs.[i] in
  xs.[i] <- v;
  bupdate (old xs) xs label b i (len xs);
  assert w = old (xs.[i])
```

## 4. A step in one basin

The functions of a time step, each with a footprint: `@owns(bed, label,
bas)` says it touches only the cells of basin `bas`, so a `spread` over
basins may call it for its own basin (ADR 0060). Each conserves the
basin's total.

The load of cell a moves into the inflow of cell b, both in basin bas.

```pia
let bpush (load : borrowed inout mutable [u32]) (inflow : borrowed inout mutable [u32]) (label : [usize]) (bas : usize) (a : usize) (b : usize) : unit @owns(load, label, bas) @owns(inflow, label, bas)
  requires a < len load && b < len inflow && len load <= max u32 + 1 && len inflow = len load && len label = len load
  requires label.[a] = bas && label.[b] = bas
  requires bsum load label bas (len load) + bsum inflow label bas (len inflow) <= max u32
  ensures load.[a] = 0
  ensures forall (k in 0 .. len load). k <> a ==> load.[k] = old (load.[k])
  ensures bsum load label bas (len load) + bsum inflow label bas (len inflow) = bsum (old load) label bas (len load) + bsum (old inflow) label bas (len inflow)
= let m = load.[a] in
  let w = inflow.[b] in
  belt_le load label bas a (len load);
  belt_le inflow label bas b (len inflow);
  bset load label bas a 0;
  bset inflow label bas b (w + m)
```

The load of an outlet of basin bas leaves the map.

```pia
let bdrain (load : borrowed inout mutable [u32]) (label : [usize]) (bas : usize) (a : usize) (gone : u64) : u64 @owns(load, label, bas)
  requires a < len load && len load <= max u32 + 1 && len label = len load && label.[a] = bas
  requires bsum load label bas (len load) + gone <= max u32
  ensures load.[a] = 0
  ensures forall (k in 0 .. len load). k <> a ==> load.[k] = old (load.[k])
  ensures bsum load label bas (len load) + result = bsum (old load) label bas (len load) + gone
= let m = load.[a] in
  belt_le load label bas a (len load);
  bset load label bas a 0;
  gone + m
```

A cell of basin bas takes its inflow and erodes or deposits.

```pia
let berode (bed : borrowed inout mutable [u32]) (load : borrowed inout mutable [u32]) (inflow : borrowed inout mutable [u32]) (label : [usize]) (bas : usize) (c : usize) (capacity : u32) : unit @owns(bed, label, bas) @owns(load, label, bas) @owns(inflow, label, bas)
  requires c < len bed && len load = len bed && len inflow = len bed && len label = len bed
  requires len bed <= max u32 + 1 && label.[c] = bas
  requires bsum bed label bas (len bed) + bsum inflow label bas (len inflow) <= max u32
  requires load.[c] = 0
  ensures inflow.[c] = 0
  ensures forall (k in 0 .. len load). k <> c ==> load.[k] = old (load.[k])
  ensures bsum bed label bas (len bed) + bsum load label bas (len load) + bsum inflow label bas (len inflow) =
    bsum (old bed) label bas (len bed) + bsum (old load) label bas (len load) + bsum (old inflow) label bas (len inflow)
= let i = inflow.[c] in
  let d = bed.[c] in
  belt_le bed label bas c (len bed);
  belt_le inflow label bas c (len inflow);
  let r = erode_or_deposit i capacity d in
  bset bed label bas c r.bed;
  assert bsum bed label bas (len bed) + d = bsum (old bed) label bas (len bed) + r.bed;
  bset load label bas c r.load;
  assert bsum load label bas (len load) = bsum (old load) label bas (len load) + r.load;
  bset inflow label bas c 0;
  assert bsum inflow label bas (len inflow) + i = bsum (old inflow) label bas (len inflow);
  balance (bsum bed label bas (len bed)) (bsum load label bas (len load)) (bsum inflow label bas (len inflow))
    (bsum (old bed) label bas (len bed)) (bsum (old load) label bas (len load)) (bsum (old inflow) label bas (len inflow))
    d i r.bed r.load
```

One transfer within basin bas.

```pia
let btransfer (bed : [u32]) (load : borrowed inout mutable [u32]) (inflow : borrowed inout mutable [u32]) (label : [usize]) (bas : usize) (a : usize) (b : usize) (outlet : bool) (gone : u64) : u64 @owns(bed, label, bas) @owns(load, label, bas) @owns(inflow, label, bas)
  requires a < len load && b < len inflow && len bed = len load && len inflow = len load && len label = len load
  requires len load <= max u32 + 1 && label.[a] = bas && label.[b] = bas
  requires bsum bed label bas (len bed) + bsum load label bas (len load) + bsum inflow label bas (len inflow) + gone <= max u32
  ensures load.[a] = 0
  ensures forall (k in 0 .. len load). k <> a ==> load.[k] = old (load.[k])
  ensures bsum bed label bas (len bed) + bsum load label bas (len load) + bsum inflow label bas (len inflow) + result =
    bsum bed label bas (len bed) + bsum (old load) label bas (len load) + bsum (old inflow) label bas (len inflow) + gone
= if outlet then bdrain load label bas a gone
  else (bpush load inflow label bas a b; gone)
```

One cell of a step within basin bas.

```pia
let bvisit (bed : borrowed inout mutable [u32]) (load : borrowed inout mutable [u32]) (inflow : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32]) (label : [usize]) (bas : usize) (c : usize) (d : usize) (capacity : u32) (gone : u64) : u64 @owns(bed, label, bas) @owns(load, label, bas) @owns(inflow, label, bas) @owns(flux, label, bas)
  requires c < len bed && d < len bed && len load = len bed && len inflow = len bed && len flux = len bed && len label = len bed
  requires len bed <= max u32 + 1 && label.[c] = bas && label.[d] = bas
  requires load.[c] = 0
  requires bsum bed label bas (len bed) + bsum load label bas (len load) + bsum inflow label bas (len inflow) + gone <= max u32
  ensures load.[c] = 0
  ensures forall (k in 0 .. len load). k <> c ==> load.[k] = old (load.[k])
  ensures bsum bed label bas (len bed) + bsum load label bas (len load) + bsum inflow label bas (len inflow) + result =
    bsum (old bed) label bas (len bed) + bsum (old load) label bas (len load) + bsum (old inflow) label bas (len inflow) + gone
= berode bed load inflow label bas c capacity;
  chain (bsum (old bed) label bas (len bed)) (bsum (old load) label bas (len load)) (bsum (old inflow) label bas (len inflow)) gone
    (bsum bed label bas (len bed)) (bsum load label bas (len load)) (bsum inflow label bas (len inflow));
  flux.[c] <- load.[c];
  let r = btransfer bed load inflow label bas c d (d = c) gone in
  r
```

One time step over basin bas: its cells, places lo up to hi of the grouped
order, highest first. Conserves the basin's total.

```pia
let btransport (fill : [u16]) (down : [usize]) (acc : [u32]) (border : [usize]) (label : [usize]) (bas : usize) (lo : usize) (hi : usize)
    (bed : borrowed inout mutable [u32]) (load : borrowed inout mutable [u32]) (inflow : borrowed inout mutable [u32]) (flux : borrowed inout mutable [u32]) (gone : u64) : u64
    @owns(bed, label, bas) @owns(load, label, bas) @owns(inflow, label, bas) @owns(flux, label, bas)
  requires len down = len fill && len acc = len fill && len border = len fill && len label = len fill
  requires len bed = len fill && len load = len fill && len inflow = len fill && len flux = len fill
  requires len fill <= max u32 + 1 && lo <= hi && hi <= len border
  requires forall (k in 0 .. len down).
             down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len label). label.[at down k] = label.[k]
  requires forall (q in lo .. hi). border.[q] < len fill && label.[border.[q]] = bas
  requires forall (k in 0 .. len load). label.[k] = bas ==> load.[k] = 0
  requires bsum bed label bas (len bed) + bsum load label bas (len load) + bsum inflow label bas (len inflow) + gone <= max u32
  ensures forall (k in 0 .. len load). label.[k] = bas ==> load.[k] = 0
  ensures bsum bed label bas (len bed) + bsum load label bas (len load) + bsum inflow label bas (len inflow) + result =
    bsum (old bed) label bas (len bed) + bsum (old load) label bas (len load) + bsum (old inflow) label bas (len inflow) + gone
=
  let g : mutable u64 = gone in
  for p in lo .. hi
    invariant forall (k in 0 .. len load). label.[k] = bas ==> load.[k] = 0
    invariant bsum bed label bas (len bed) + bsum load label bas (len load) + bsum inflow label bas (len inflow) + g =
      bsum (old bed) label bas (len bed) + bsum (old load) label bas (len load) + bsum (old inflow) label bas (len inflow) + gone
  do
    let c = border.[p] in
    let d = down.[c] in
    assert label.[at down c] = label.[c];
    let drop : u16 = if d = c then 0 else fill.[c] - fill.[d] in
    g <- bvisit bed load inflow flux label bas c d (capacity_of acc.[c] drop) g
  done;
  g
```

## 5. Every basin at once

`lsum` is the sum of the cells whose label is below `nb`. Splitting off
the last basin, and taking every label, show that the basins' sums add up
to the whole sum, and `lsum_balance` adds the per-basin laws up into the
law for the map.

The sum of the cells among xs.[0 .. n] whose label is below nb.

```pia
let spec lsum (xs : [u32]) (label : [usize]) (nb : usize) (n : usize) : u64
  requires n <= len xs && len label = len xs && n <= max u32 + 1
  ensures result <= sum xs n
  decreases n
= if n = 0 then 0 else lsum xs label nb (n - 1) + (if label.[n - 1] < nb then elt xs (n - 1) else 0)
```

Splitting off the last basin: the cells below nb are those below nb - 1 and
those of basin nb - 1.

```pia
let lemma lsum_split (xs : [u32]) (label : [usize]) (nb : usize) (n : usize) : unit
  requires 0 < nb && n <= len xs && len label = len xs && n <= max u32 + 1
  ensures lsum xs label nb n = lsum xs label (nb - 1) n + bsum xs label (nb - 1) n
  decreases n
= if n > 0 then lsum_split xs label nb (n - 1)
```

When every label is below nb, the cells below nb are all of them.

```pia
let lemma lsum_all (xs : [u32]) (label : [usize]) (nb : usize) (n : usize) : unit
  requires n <= len xs && len label = len xs && n <= max u32 + 1
  requires forall (k in 0 .. n). at label k < nb
  ensures lsum xs label nb n = sum xs n
  decreases n
= if n > 0 then (lsum_all xs label nb (n - 1); assert at label (n - 1) < nb)
```

The arithmetic of one basin more.

```pia
let lemma add_basin (l1 : u64) (l2 : u64) (l3 : u64) (g : u64) (m1 : u64) (m2 : u64) (m3 : u64)
    (b1 : u64) (b2 : u64) (b3 : u64) (gb : u32) (c1 : u64) (c2 : u64) (c3 : u64)
    (n1 : u64) (n2 : u64) (n3 : u64) (h : u64) (k1 : u64) (k2 : u64) (k3 : u64) : unit
  requires l1 + l2 + l3 + g = m1 + m2 + m3
  requires b1 + b2 + b3 + gb = c1 + c2 + c3
  requires n1 = l1 + b1 && n2 = l2 + b2 && n3 = l3 + b3 && h = g + gb
  requires k1 = m1 + c1 && k2 = m2 + c2 && k3 = m3 + c3
  ensures n1 + n2 + n3 + h = k1 + k2 + k3
= ()
```

One basin more, without the quantifier.

```pia
let lemma balance_step (bed : [u32]) (load : [u32]) (inflow : [u32]) (bed0 : [u32]) (load0 : [u32]) (inflow0 : [u32])
    (gone : [u32]) (label : [usize]) (nb : usize) : unit
  requires len load = len bed && len inflow = len bed && len bed0 = len bed && len load0 = len bed
  requires len inflow0 = len bed && len label = len bed && len bed <= max u32 + 1
  requires 0 < nb && nb <= len gone && len gone <= max u32 + 1
  requires lsum bed label (nb - 1) (len bed) + lsum load label (nb - 1) (len bed) + lsum inflow label (nb - 1) (len bed) + sum gone (nb - 1) =
    lsum bed0 label (nb - 1) (len bed) + lsum load0 label (nb - 1) (len bed) + lsum inflow0 label (nb - 1) (len bed)
  requires bsum bed label (nb - 1) (len bed) + bsum load label (nb - 1) (len bed) + bsum inflow label (nb - 1) (len bed) + gone.[nb - 1] =
    bsum bed0 label (nb - 1) (len bed) + bsum load0 label (nb - 1) (len bed) + bsum inflow0 label (nb - 1) (len bed)
  ensures lsum bed label nb (len bed) + lsum load label nb (len bed) + lsum inflow label nb (len bed) + sum gone nb =
    lsum bed0 label nb (len bed) + lsum load0 label nb (len bed) + lsum inflow0 label nb (len bed)
= lsum_split bed label nb (len bed); lsum_split load label nb (len bed); lsum_split inflow label nb (len bed);
  lsum_split bed0 label nb (len bed); lsum_split load0 label nb (len bed); lsum_split inflow0 label nb (len bed);
  assert sum gone nb = sum gone (nb - 1) + gone.[nb - 1];
  add_basin (lsum bed label (nb - 1) (len bed)) (lsum load label (nb - 1) (len bed)) (lsum inflow label (nb - 1) (len bed)) (sum gone (nb - 1))
    (lsum bed0 label (nb - 1) (len bed)) (lsum load0 label (nb - 1) (len bed)) (lsum inflow0 label (nb - 1) (len bed))
    (bsum bed label (nb - 1) (len bed)) (bsum load label (nb - 1) (len bed)) (bsum inflow label (nb - 1) (len bed)) gone.[nb - 1]
    (bsum bed0 label (nb - 1) (len bed)) (bsum load0 label (nb - 1) (len bed)) (bsum inflow0 label (nb - 1) (len bed))
    (lsum bed label nb (len bed)) (lsum load label nb (len bed)) (lsum inflow label nb (len bed)) (sum gone nb)
    (lsum bed0 label nb (len bed)) (lsum load0 label nb (len bed)) (lsum inflow0 label nb (len bed))
```

The per-basin laws, summed over the basins below nb.

```pia
let lemma lsum_balance (bed : [u32]) (load : [u32]) (inflow : [u32]) (bed0 : [u32]) (load0 : [u32]) (inflow0 : [u32])
    (gone : [u32]) (label : [usize]) (nb : usize) : unit
  requires len load = len bed && len inflow = len bed && len bed0 = len bed && len load0 = len bed
  requires len inflow0 = len bed && len label = len bed && len bed <= max u32 + 1
  requires nb <= len gone && len gone <= max u32 + 1
  requires forall (b in 0 .. nb).
    bsum bed label b (len bed) + bsum load label b (len bed) + bsum inflow label b (len bed) + gone.[b] =
    bsum bed0 label b (len bed) + bsum load0 label b (len bed) + bsum inflow0 label b (len bed)
  ensures lsum bed label nb (len bed) + lsum load label nb (len bed) + lsum inflow label nb (len bed) + sum gone nb =
    lsum bed0 label nb (len bed) + lsum load0 label nb (len bed) + lsum inflow0 label nb (len bed)
  decreases nb
= if nb > 0 then (
    lsum_balance bed load inflow bed0 load0 inflow0 gone label (nb - 1);
    assert bsum bed label (nb - 1) (len bed) + bsum load label (nb - 1) (len bed) + bsum inflow label (nb - 1) (len bed) + gone.[nb - 1] =
      bsum bed0 label (nb - 1) (len bed) + bsum load0 label (nb - 1) (len bed) + bsum inflow0 label (nb - 1) (len bed);
    balance_step bed load inflow bed0 load0 inflow0 gone label nb)
```

A basin's sum is at most the whole sum.

```pia
let lemma bsum_le (xs : [u32]) (label : [usize]) (b : usize) (n : usize) : unit
  requires n <= len xs && len label = len xs && n <= max u32 + 1
  ensures bsum xs label b n <= sum xs n
  decreases n
= if n > 0 then bsum_le xs label b (n - 1)
```

A basin's outflow is at most the whole map's total.

```pia
let lemma outflow_fits (a : u64) (b : u64) (c : u64) (g : u64) (a0 : u64) (b0 : u64) (c0 : u64) (s1 : u64) (s2 : u64) (s3 : u64) : unit
  requires a + b + c + g = a0 + b0 + c0
  requires a0 <= s1 && b0 <= s2 && c0 <= s3 && s1 + s2 + s3 <= max u32
  ensures g <= max u32
= ()
```

steps time steps over every basin at once, each basin on its own: a spread
over the basins (ADR 0060), with the basin labels as the owner of bed,
load, inflow and flux, and each basin's outflow in its own cell of gone_by.
Each basin conserves its total, and the totals add up to the whole map's.

```pia
let transport_basins (fill : [u16]) (down : [usize]) (acc : [u32]) (border : [usize]) (label : [usize])
    (first : [usize]) (last : [usize]) (gowner : [usize]) (steps : u32)
    (bed : borrowed inout mutable [u32]) (load : borrowed inout mutable [u32]) (inflow : borrowed inout mutable [u32])
    (flux : borrowed inout mutable [u32]) (gone_by : borrowed inout mutable [u32]) : unit
  requires len down = len fill && len acc = len fill && len border = len fill && len label = len fill
  requires len first = len fill && len last = len fill && len gowner = len fill && len gone_by = len fill
  requires len bed = len fill && len load = len fill && len inflow = len fill && len flux = len fill
  requires len fill <= max u32
  requires forall (k in 0 .. len down).
             down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len label). label.[at down k] = label.[k] && at label k < len fill
  requires forall (b in 0 .. len fill). first.[b] <= last.[b] && last.[b] <= len fill
  requires forall (q in 0 .. len border). border.[q] < len fill && label.[border.[q]] = at gowner q
  requires forall (b in 0 .. len fill) (q in 0 .. len border). first.[b] <= q && q < last.[b] ==> at gowner q = b
  requires forall (k in 0 .. len load). load.[k] = 0
  requires sum bed (len bed) + sum load (len load) + sum inflow (len inflow) <= max u32
  ensures sum bed (len bed) + sum load (len load) + sum inflow (len inflow) + sum gone_by (len gone_by) =
    sum (old bed) (len bed) + sum (old load) (len load) + sum (old inflow) (len inflow)
= let n = len fill in
  spread b in 0 .. n @owns(bed, label) @owns(load, label) @owns(inflow, label) @owns(flux, label)
    ensures bsum bed label b n + bsum load label b n + bsum inflow label b n + gone_by.[b] =
      bsum (old bed) label b n + bsum (old load) label b n + bsum (old inflow) label b n
  do
    let lo = first.[b] in
    let hi = last.[b] in
    assert (forall (q in lo .. hi). border.[q] < n && label.[border.[q]] = b);
    bsum_le (old bed) label b n; bsum_le (old load) label b n; bsum_le (old inflow) label b n;
    let g : mutable u64 = 0 in
    for s in 0 .. steps
      invariant forall (k in 0 .. len load). label.[k] = b ==> load.[k] = 0
      invariant bsum bed label b n + bsum load label b n + bsum inflow label b n + g =
        bsum (old bed) label b n + bsum (old load) label b n + bsum (old inflow) label b n
    do
      g <- btransport fill down acc border label b lo hi bed load inflow flux g
    done;
    outflow_fits (bsum bed label b n) (bsum load label b n) (bsum inflow label b n) g
      (bsum (old bed) label b n) (bsum (old load) label b n) (bsum (old inflow) label b n)
      (sum (old bed) n) (sum (old load) n) (sum (old inflow) n);
    let gb : u32 = g in
    gone_by.[b] <- gb
  done;
  lsum_balance bed load inflow (old bed) (old load) (old inflow) gone_by label n;
  lsum_all bed label n n; lsum_all load label n n; lsum_all inflow label n n;
  lsum_all (old bed) label n n; lsum_all (old load) label n n; lsum_all (old inflow) label n n
```

steps time steps of sediment transport, every basin on its own core, from
the sediment in bed with no load and no inflow. label, order and down come
from the first half and from `drainage` (sediment.pia.md): every cell's
basin is an outlet below len fill, a cell and the cell it drains to share a
basin, and order names cells. The result is the mass that left the map, and
the total is conserved exactly; if the total does not fit in a u32, nothing
moves and the result is 2^64 - 1.

```pia
let sediment_basins (fill : [u16]) (down : [usize]) (acc : [u32]) (label : [usize]) (order : [usize]) (steps : u32)
    (bed : borrowed inout mutable [u32]) (load : out mutable [u32]) (inflow : out mutable [u32])
    (flux : out mutable [u32]) (gone_by : out mutable [u32])
    (border : out mutable [usize]) (keys : out mutable [usize]) (place2 : out mutable [usize]) (pos2 : out mutable [usize])
    (cnt : out mutable [u32]) (first : out mutable [usize]) (next : out mutable [usize]) (last : out mutable [usize])
    (gowner : out mutable [usize]) : u64
  requires len down = len fill && len acc = len fill && len label = len fill && len order = len fill
  requires len bed = len fill && len load = len fill && len inflow = len fill && len flux = len fill && len gone_by = len fill
  requires len border = len fill && len keys = len fill && len place2 = len fill && len pos2 = len fill
  requires len cnt = len fill && len first = len fill && len next = len fill && len last = len fill && len gowner = len fill
  requires len fill >= 1 && len fill < max u32
  requires forall (k in 0 .. len down).
             down.[k] = k || (down.[k] < len fill && fill.[down.[k]] < fill.[k])
  requires forall (k in 0 .. len label). label.[at down k] = label.[k] && at label k < len fill
  requires forall (q in 0 .. len order). order.[q] < len fill
  ensures result = max u64 ||
    sum bed (len bed) + sum load (len load) + sum inflow (len inflow) + result = sum (old bed) (len bed)
=
  for i in 0 .. len fill
    invariant forall (k in 0 .. i). load.[k] = 0 && inflow.[k] = 0 && flux.[k] = 0 && gone_by.[k] = 0
  do
    load.[i] <- 0;
    inflow.[i] <- 0;
    flux.[i] <- 0;
    gone_by.[i] <- 0
  done;
  zero load (len load);
  zero inflow (len inflow);
  let t = total bed in
  if t > max u32 then max u64
  else (
    basin_order label order border keys place2 pos2 cnt first next last gowner;
    transport_basins fill down acc border label first last gowner steps bed load inflow flux gone_by;
    total gone_by)
```

## What is proved

| Goal | Where |
| --- | --- |
| Every index is in bounds, nothing overflows | every function |
| Grouping by basin puts exactly basin b's cells in its range of places | `ghistogram` up to `basin_order` |
| A write to a basin's cell changes its sum by the new value less the old, and a write elsewhere leaves it alone | `bupdate`, `bset`, and `bsum`'s frame lemma |
| Each step in a basin conserves the basin's total | `bpush` up to `btransport` |
| No two basins touch the same cell, so the `spread` has no race | the footprints and `@owns(_, label)` |
| The basins' totals add up to the map's, and the map's total is conserved exactly | `lsum_balance`, `transport_basins`, `sediment_basins` |
