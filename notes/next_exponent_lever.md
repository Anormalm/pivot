# Revised exponent route: improve FindPivots coefficient, not BM.6

**Status:** research target derived from the corrected amortized accounting.

## 1. What survives after the N4 tightening

The direct N4 refinement removes the once-per-group expensive **re-selection**
charge for full calls:

```
g_j <= c_j.
```

But BM.6 still creates Theta(t p)-scale DLazy potential in the existing
amortized proof. Therefore the master expression still contains the
initialization contribution corresponding to

```
N * L * t/k.
```

Removing the N4 `+1` alone therefore does not change the old
`k ~ sqrt(t)` optimum.

## 2. Parameterize the FindPivots cost by A(k)

Upstream `fpC_spec` has the exact form

```
FindPivotsCost
  <= deletion_charge
     + fpA(k) * (#tree_vertices + k * |Q|)
     + O(|S|).
```

Current C-HD proves

```
fpA(k) = Theta(k).
```

The resulting core menu is schematically

```
N L * (A(k) + t/k)
+ A(k) * k * (m + N L/t)
+ m t
+ lower-order terms.
```

For the current `A(k)=Theta(k)`, this is exactly the familiar

```
N L * (k + t/k)
+ k^2 * (m + N L/t)
+ m t.
```

## 3. If A(k) becomes O(1) or O(log k)

Take

```
k = t.
```

If `A(k)=O(1)`, the menu becomes

```
N L
+ N L
+ t * (m + N L/t)
+ m t
=
O(N log N / t + m t).
```

Balancing at

```
t = sqrt(N log N / m)
```

gives

```
O(sqrt(m N log N)).
```

Crucially, the BM.6 initialization term remains present; it is simply reduced
by the larger choice `k=t`.

If instead

```
A(k)=O(log k),
```

the same choice gives approximately

```
O((N log N / t + m t) * log t),
```

which is a square-root-type bound with an extra log-log factor. In the
showcase density `m=n log^(3/4)n`, this is

```
n log^(7/8)n * log log n,
```

still asymptotically below `n log^(11/12)n`.

## 4. Where current A(k)=Theta(k) comes from

This is not mainly the unsorted-array ExtractMin.

In `FindPivots.lean`:

```
extC(K) =
  (scanC + hins) * (1 + K)
  + hext + 1.
```

Then `search_cost_le` pays

```
extC(k) * k.
```

The `(1+K)` factor comes from the bound

```
out(u).countP(dst in K) <= |K|.
```

That is: during each extraction, the implementation may scan Theta(k) edges
whose heads are already members of the current local search. Across Theta(k)
extracted vertices this gives Theta(k^2) internal-edge work.

Replacing the unsorted-array heap only changes `hext`; it does **not**
remove this scan factor.

## 5. Actual second research problem

The exponent-level question is now:

> Can the repeated/in-K edge scans of FindPivots-HD be separated from the
> per-vertex charge and amortized globally, cached safely, or handled by a
> different local-search organization?

A useful target theorem would replace

```
fpA(k) * (#tv + k|Q|)
with fpA(k)=Theta(k)
```

by something like

```
O(polylog k) * (#tv + k|Q|)
+ O(number of newly processed graph edges).
```

For this to improve the full algorithm, the extra edge term must itself have
a global O(m t)-type charge; merely paying O(m) per invocation or per level is
not enough.

## 6. Why caching is nontrivial

An edge already scanned for relaxation need not be useful to relax again if:

- the tail label is unchanged (the candidate is unchanged);
- target labels only decrease, so a previously non-improving candidate never
  becomes improving.

However two things can invalidate naive caching:

1. the tail label may later decrease, which lowers all outgoing candidates;
2. the global FindPivots tree set T grows, so an edge that was previously an
   ordinary scan can later become a contact edge.

This suggests a possible decomposition:

- cache relaxation work by tail-label version;
- handle newly created tree contacts separately, perhaps through reverse-edge
  notification when vertices enter T.

That is the next concrete algorithmic direction to test.

## 7. Revised claim discipline

Current strong result:

```
full-call N4 re-selections: g_j <= c_j
```

Current blocker:

```
BM.6 existing DLazy potential: Theta(t p) scale can remain.
```

Current exponent route:

```
reduce FindPivots A(k) from Theta(k) to polylog(k) or O(1),
then choose k=t.
```

So the square-root bound remains a research target, but the needed second
ingredient is now much more precisely identified.
