# Why the N4 tightening alone cannot change the C-HD exponent

The N4 correction removes the once-per-group **re-selection** contribution,
but the existing master expression still contains two independent terms:

1. initial-pivot ordering / BM.6-D work;
2. local FindPivots search work.

Ignoring constants and lower-order terms, these include

```text
T >= / contains
  N log n / k
  + m k^2.
```

The first term is the hierarchy-wide form of the remaining O(t p) initial
pivot charge:

```text
(L+1) * N * t/k
  with L = Theta(log n / t)
  = Theta(N log n / k).
```

The second is the existing failed-search/local-search term.

Now put

```text
m = n log^alpha n
k = log^gamma n.
```

The two log exponents are

```text
pivot ordering:  1 - gamma
local searches:  alpha + 2 gamma.
```

Minimizing their maximum balances them:

```text
1 - gamma = alpha + 2 gamma
gamma = (1-alpha)/3.
```

The resulting exponent is

```text
1 - gamma
  = (2+alpha)/3.
```

This is exactly the current C-HD exponent.

At alpha=3/4:

```text
gamma = 1/12
exponent = 11/12.
```

Therefore, even if every other term were made lower order, **removing the N4
re-selection +p term alone does not change the asymptotic optimum** as long
as the BM.6 ordered-pivot term and O(k^2) local-search term remain.

This is a statement about the current master-term structure, not a lower
bound for all possible shortest-path algorithms.

## What must change for a better exponent

At least one of the two structural terms must be improved:

- reduce the hierarchy-wide pivot-ordering term below N log n / k; or
- make the bounded FindPivots search subquadratic in k.

The tradeoff is quantified in `notes/local_search_tradeoff.md`.

This explains why the initially proposed 11/12 -> 7/8 jump required both the
N4 correction and a second, genuinely algorithmic improvement.
