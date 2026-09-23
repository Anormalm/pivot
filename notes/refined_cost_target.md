# Refined final per-call cost target

The candidate proof should ultimately replace the current recursive
`CostAggregate.Valid.cost_le` budget

```text
(k+1)(U+Fo)
+ S
+ t Q
+ t(J+Wr+Cr+Be)
+ t p
+ [partial] t S
+ merge
+ Del
```

by

```text
(k+1)(U+Fo)
+ S
+ t Q
+ t(J+Wr+Cr+Be)
+ [partial] t S
+ merge
+ Del.
```

The unconditional `t p` term disappears.

## Why every remaining pivot term still fits

### Full calls

The existing full-call pivot bound is

```text
p (k-1) <= U + Fo.
```

For `k>=2`,

```text
k p <= 2(U+Fo),
```

so all **cheap** `O(k p)` pivot/group work is absorbed into the existing
`(k+1)(U+Fo)` part up to a constant.

The expensive `I p = O(t p)` work is exactly what the new credit/home
cancellation removes:

```text
cost + I p
  <= cheap + I(mkOf + ownGroups) + ...
  <= cheap + I p + I(Cr+Be) + ...
```

and the `I p` terms cancel.

### Partial calls

Upstream already has

```text
p <= |S|
t |S| <= |U|
```

in the relevant partial-call accounting, together with `3k <= t`.

Thus

```text
O(k p) <= O(t |S|)
```

and any residual generic insertion work proportional to `p` is also
covered by the existing partial `t|S|` term.

No separate global `t p` term is needed.

## Initialization

BM.6 initial pivot insertions are not part of the expensive evolved-structure
charge. Existing DLazy facts give `O(1)` per pivot on the fresh one-block
structure.

So the initialization budget should contain only

```text
O(p) + sum_j |P_j|,
```

not `I p`.

Since the groups are disjoint subsets of `S`,

```text
p <= |S|,
sum_j |P_j| <= |S|,
```

and initialization is absorbed by the ordinary `S` term.

## Refined global master expression

After these changes, the visible terms reduce to

```text
(L+1) N k
+ k^2 (m + N L/t)
+ m t
+ m log(t delta)
+ lower-order terms.
```

For constant `k=4` and `L=Theta(log N/t)`:

```text
N log N/t
+ m
+ N log N/t^2
+ m t
+ m log(t delta).
```

With the new parameter condition

```text
log N <= t^2 d
```

the failed-search correction `N log N/t^2` is `O(m)`.

The dominant balance is therefore

```text
N log N/t + m t,
```

optimized at

```text
t = Theta(sqrt(N log N/m)).
```
