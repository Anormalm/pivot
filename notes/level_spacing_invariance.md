# Level-spacing invariance of the ordered-pivot term

A natural response to the BM.6 fresh-block blocker is to reduce the ratio
between adjacent level capacities.

Current C-HD uses roughly

  M_{l+1} / M_l = 2^t.

A child call at level l can receive O(k M_{l+1}) frontier vertices and hence
O(M_{l+1}) pivot groups.  Its fresh D structure uses block parameter M_l, so

  p_l / M_l = O(M_{l+1}/M_l).

The comparison / potential cost per initial pivot is therefore controlled by

  log(M_{l+1}/M_l).

## General nonuniform hierarchy

Let

  r_l = M_{l+1}/M_l.

Suppose we redesign the hierarchy with smaller or nonuniform ratios.  The
fresh ordered-pivot term at level l becomes schematically

  O(p_l log r_l).

The full-call pivot-count charging gives O(N/k) pivot mass per layer, so a
natural global contribution is

  O((N/k) * sum_l log r_l).

But the level capacities telescope:

  product_l r_l = M_top / M_base,

hence

  sum_l log r_l = log(M_top/M_base).

To cover the full problem, M_top/M_base is polynomial in n, so this is
Theta(log n) regardless of how the ratio is distributed among levels.

Therefore the hierarchy-wide term remains

  Theta(N log n / k)

up to constants/lower-order factors.

## Interpretation

Using a smaller adjacent-level ratio:

- reduces the fresh-block oversize and per-level ordering charge;
- increases the number of levels by the compensating factor.

Using a larger ratio does the opposite.

So simply retuning the level spacing cannot remove the ordered-pivot term.
A genuine improvement has to reduce the amount of comparison information
extracted from the pivots, reduce pivot mass, or exploit additional order
already known from elsewhere.

This is the hierarchy analogue of the exact PullSpec ordered-bucket barrier.
