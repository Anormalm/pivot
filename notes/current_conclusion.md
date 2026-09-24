# Current conclusion

Date: 2026-09-24

This repository started from the suspicion that C-HD's full-call pivot
accounting had enough slack to change the final exponent.  The investigation
now separates into one verified tightening and one harder algorithmic
question.

## 1. Verified tightening: N4 loses an unnecessary +1

For a full-call pivot group, upstream Appendix N4 proves

```text
g_j <= c_j + 1.
```

BM.23 re-selects only while the residual group is nonempty.  Therefore the
g_j re-selection homes cannot exhaust all home-components touched by the
group: there is always a terminal home, either the child that empties the
group or W'/home-0 if the group survives the child loop.

Hence

```text
g_j + 1 <= c_j + 1
```

and therefore

```text
g_j <= c_j.
```

The corresponding finite-set, loop-credit, own-home, recursive-cost and
budget lemmas compile together against the pinned upstream C-HD snapshot.
The full candidate Lean workflow is green at run `36021686384`.

So this is no longer merely an experiment or paper intuition: the local
full-call cost tightening has a hole-free, kernel-checked candidate proof
chain.

## 2. Why this alone does not change the exponent

C-HD has another full-call pivot term from BM.6 / the D structure.

The physical insertion of a pivot into a fresh one-block DLazy structure is
constant-time, but the amortized proof must also pay the potential created by
that oversized block.

For a child call X of parent Z,

```text
|S_X| <= 3 k M_Z,
p_X <= |S_X|,
```

while X's fresh structure uses M_X.  At recursive levels,

```text
M_Z / M_X = 2^t.
```

Thus p_X/M_X can be O(k 2^t), so the fresh-block potential contains

```text
ell(M_X,p_X) = Theta(t + log k)
```

in the worst allowed regime.

The initIns patch fails exactly at this amortized-potential boundary in
`BMTeleLoop`.

## 3. This potential reflects real work in the current D implementation

The experiment `split_work_growth.py` models an idealized sequence of
perfectly balanced median splits and counts only one linear scan per split.
Exhausting an oversized block still costs

```text
Theta(p log(p/M)).
```

So the issue is not merely that C-HD chose a loose potential function.

## 4. The abstract Pull interface also contains comparison information

`PullSpec` requires each pull to return **exactly all stored keys below a
separator**.  With p arbitrary distinct keys and batch size M, consuming all
keys identifies their ordered M-sized rank buckets.

For p=qM, the number of possible ordered bucketings is

```text
p! / (M!)^q,
```

whose comparison information is

```text
Theta(p log(p/M)).
```

MakePivots does not provide a free ordering: groups are emitted in tree-piece
order and their pivot minima are chosen afterward.

This suggests that a priority-structure-only replacement cannot in general
turn the current exact ordered-pull architecture into O(p) work.

## 5. The other route to a better exponent is also structural

Write the local FindPivots search cost as O(k^q).  The master balance for

```text
m = n log^alpha n
```

optimizes to the log exponent

```text
(q + alpha)/(q + 1).
```

At alpha=3/4:

```text
q=2    -> 11/12
q=1.5  -> 0.9
q=1    -> 7/8.
```

But the current HD1 bounded Dijkstra search can inspect Theta(k^2) relevant
weighted edges in a dense k-vertex region.  The persistent main-recursion
`ptr[u]` optimization does not apply: the paper explicitly says FindPivots
FH.7 scans the mutable list and never advances that static pointer.

Thus a near-linear local search would also require new algorithmic structure,
not just a better heap.

## 6. Practical conclusion

The defensible contribution today is:

> C-HD's full-call N4 re-selection analysis can be tightened from
> g_j <= c_j+1 to g_j <= c_j, and the corresponding local/recursive
> accounting patch has been kernel-checked against the released proof
> snapshot.

The stronger statement

```text
O(sqrt(m n log n))
```

is still a research target.  Reaching it appears to require changing one of
the architecture's two ordering/dense-search bottlenecks:

1. avoid exact ordered processing of all initial pivots; or
2. avoid Theta(k^2) work in a worst-case dense local FindPivots search.

The repo should not claim 11/12 -> 7/8 as proved.
