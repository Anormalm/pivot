# Ordered-pull barrier for the initial pivot set

Date: 2026-09-24

## Why a different DLazy implementation alone may not remove O(t p)

The remaining BM.6 issue is not just that the current potential is large.

The abstract BMSSP loop asks its D structure to satisfy `PullSpec`:

```text
S' = exactly the stored keys with value < separator x,
D' = D with exactly S' removed,
x <= bound.
```

The concrete cost contract additionally gives at most M pulled keys, and a
short pull exhausts the structure.  Thus, on a structure with p distinct
live pivot keys and no intervening deletions, successive pulls identify the
keys in ordered value buckets of size M (except possibly the last bucket).

## Comparison information in those outputs

Assume for simplicity

```text
p = q M.
```

For p distinct arbitrary keys, the sequence of exact M-key pull sets
identifies which keys belong to the first rank bucket, the second rank
bucket, ..., the q-th rank bucket.

The number of possible ordered bucketings is

```text
p! / (M!)^q.
```

A comparison decision tree distinguishing these cases therefore needs depth

```text
log2(p! / (M!)^q)
  = Theta(p log(p/M))
```

by Stirling's approximation.

So if a full execution actually consumes all p arbitrary initial pivots
through this exact ordered-pull interface, an O(p)-comparison implementation
cannot exist in general.

This matches both:

- the existing DLazy potential term
  `S_M(p) = Theta(p log(p/M))`; and
- the idealized balanced-split experiment in
  `experiments/split_work_growth.py`.

## Are C-HD's initial pivots specially ordered?

Nothing found in the current construction supplies such an order.

`makePivots` explicitly emits groups in **tree-piece order**:

```text
groups from the pieces, in piece order
```

and its implementation depends only on tree membership plus S/Q membership.

BM.7 then chooses the minimum-label member of each group.  The group order is
therefore topological/structural, not ordered by pivot label.

At present there is no theorem or implementation invariant implying that
these p pivot labels arrive sorted, nearly sorted, or in bounded-disorder
order.

## Consequence

The direct N4 improvement `g_j <= c_j` remains valid.

But to remove the remaining full-call O(t p) term, the likely target is no
longer "make fresh insertion cheaper."  One of the following must change:

1. **Avoid exact ordered pulls for all initial pivots.**
   Change BMSSP so that it does not need to rank-partition every initial
   pivot into M-sized value batches.

2. **Exploit additional structure in pivot labels.**
   Prove a property stronger than currently known that reduces their
   comparison entropy.  The present MakePivots construction does not expose
   such a property.

3. **Avoid consuming all initial pivots.**
   Show that, on every full call, a large fraction can be discharged/deleted
   without participating in the ordered-pull sequence, with a global charge
   strong enough to beat p log(p/M).

4. **Change the recursive frontier mechanism.**
   Replace the exact Dijkstra-like PullSpec with a weaker batching interface
   while reproving the frontier/correctness and handled-range accounting.

The fourth direction is the most invasive, but the comparison argument above
suggests that a purely local priority-structure replacement will not yield
the hoped-for O(p) initialization in the worst case.

## Status

This is an information-theoretic argument about the current **ordered-pull
interface**, not yet a formal lower bound for every valid C-HD execution.
To make it a theorem about C-HD itself one would still need a realizability
argument showing a family of full calls whose initial pivot values are
arbitrary and whose pivots are all consumed by Pull rather than removed by
other events.
