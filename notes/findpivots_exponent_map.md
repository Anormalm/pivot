# Generalized FindPivots exponent map

After the N4 tightening, retain the existing BM.6 amortized initialization
term.  Suppose a future FindPivots implementation has per-unit coefficient

```
A(k) = Theta(k^r),    0 <= r <= 1.
```

The current C-HD implementation corresponds to `r=1`.

Write

```
m = n log^alpha n
t = log^b n
k = log^c n.
```

Ignoring lower-order log-log factors, the refined master terms have log
exponents

```
N L A(k)              : 1 - b + r c
N L t/k               : 1 - c
A(k) k m              : alpha + (r+1)c
A(k) k N L/t          : 1 - 2b + (r+1)c
m t                    : alpha + b.
```

Balancing the three dominant terms gives

```
c = (1-alpha)/(r+2)
b = (r+1)(1-alpha)/(r+2).
```

Therefore the optimized exponent is

```
E(r,alpha) = (r + 1 + alpha)/(r + 2).
```

## Checks

### Current C-HD

`r=1` gives

```
E = (2+alpha)/3,
```

which recovers the current analysis exactly.

At `alpha=3/4`:

```
E = 11/12.
```

### Square-root-in-k FindPivots coefficient

`r=1/2` gives

```
E = (3/2 + alpha)/(5/2).
```

At `alpha=3/4`:

```
E = 0.9.
```

Thus even reducing the coefficient from Theta(k) to Theta(sqrt(k)) would
strictly improve the showcased exponent.

### Polylog / constant coefficient

At the log-power level, `A(k)=polylog(k)` behaves like `r=0`:

```
E = (1+alpha)/2.
```

At `alpha=3/4` this is

```
7/8,
```

with whatever extra polylog(k)=polyloglog(n) factor the local search retains.

## Interpretation

The next research goal does not need to jump directly from Theta(k) to O(1).
Any genuine power saving

```
A(k) = O(k^(1-epsilon))
```

improves the C-HD logarithmic exponent.

The exact current source of the Theta(k) coefficient is the internal-member
scan bound in `Search.cost`:

```
out(u).countP(dst in K) <= |K|.
```

That contributes the `(scanC+hins)*(1+k)` part of `extC(k)`.
The heap's O(k) ExtractMin is only one additional component.

So the next algorithmic question is quantitatively:

> Can the repeated scans of edges whose heads are already in the local K set
> be processed in O(k^(1-epsilon)) amortized work per member, or separated
> into a globally chargeable edge term?

A sqrt(k) saving is already asymptotically meaningful.
