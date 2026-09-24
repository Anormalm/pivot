# Why a naive two-parameter split does not immediately help

The master bound uses the same parameter k in two roles:

1. FindPivots local searches stop at about k discovered/extracted vertices.
2. The parent-first forest is partitioned into PT pieces of size [k,3k),
   giving p(k-1) <= #tree vertices.

It is tempting to introduce:

  k_search << k_group

so local searches stay cheap while larger groups reduce the number of
initial pivots that must be ordered by D.

The current construction does not support this for free.

A successful FindPivots search is only guaranteed to create a tree of the
search-threshold scale. The tree partition works *inside each tree*; it does
not join unrelated trees. Therefore choosing k_group substantially larger
than k_search leaves valid successful trees too small to provide the required
PT pieces/groups.

Grouping across different trees would require new connecting structure. In
particular, the N4 home-colour charge currently relies on every pivot group
being contained in one connected PT piece whose bichromatic parent edges are
actual graph edges. Artificially joining separate trees would introduce
unchargeable connector edges or a new once-per-component term.

So a useful two-parameter variant would need one of:

- a new way to merge/aggregate successful trees before MakePivots;
- a different re-selection charging argument for groups spanning components;
- or a larger local search threshold together with a cheaper local-search
  implementation.

The last option motivates auditing the current O(k^2) FindPivots search cost.
