#!/usr/bin/env python3
"""
Exhaustive sanity checks for a proposed refinement of the C-HD / BMSSP
pivot re-selection accounting.

The current C-HD analysis charges, for each pivot group, at most
    1 + (# bichromatic parent edges)
expensive re-selections.

The executable semantics re-select a group only when:
  (1) its current pivot is returned by child U_i, AND
  (2) the residual group P_j \ U_i is nonempty.

For a FULL parent call, every group member is eventually returned by either
a child or the parent's final W'. Thus the last represented "home" never
causes an expensive re-selection. This motivates
    actual re-selections <= (# represented homes in group) - 1.

Existing C-HD tree lemmas already imply
    (# represented homes in group) - 1
      <= (# bichromatic parent edges in the containing PT piece).

This script exhaustively checks the first inequality under a deliberately
more permissive model than the algorithm: pivots may be chosen arbitrarily
after every re-selection, rather than as minimum-label members.
It also checks the rooted-tree colour inequality on all parent arrays and
colourings up to configurable small sizes.
"""

from functools import lru_cache
from itertools import product

def all_parent_arrays(n):
    if n == 1:
        yield (-1,)
        return
    choices = [range(v) for v in range(1, n)]
    for ps in product(*choices):
        yield (-1,) + tuple(ps)

def bichromatic_edges(parent, colors):
    return sum(
        1 for v in range(1, len(parent))
        if colors[v] != colors[parent[v]]
    )

def check_tree_colour_bound(max_n=7, max_colors=3):
    checked = 0
    for n in range(1, max_n + 1):
        for parent in all_parent_arrays(n):
            for colors in product(range(max_colors), repeat=n):
                lhs = len(set(colors)) - 1
                rhs = bichromatic_edges(parent, colors)
                checked += 1
                if lhs > rhs:
                    return False, checked, {
                        "n": n, "parent": parent, "colors": colors,
                        "lhs": lhs, "rhs": rhs,
                    }
    return True, checked, None

def max_reselections_for_home_partition(homes):
    n = len(homes)
    H = max(homes, default=0)
    full = (1 << n) - 1

    @lru_cache(None)
    def dp(i, mask, pivot):
        if i > H or mask == 0:
            return 0
        removed = 0
        for v, h in enumerate(homes):
            if h == i and (mask >> v) & 1:
                removed |= 1 << v
        newmask = mask & ~removed

        if not ((removed >> pivot) & 1):
            return dp(i + 1, newmask, pivot) if newmask else 0
        if newmask == 0:
            return 0

        best = 0
        for q in range(n):
            if (newmask >> q) & 1:
                best = max(best, dp(i + 1, newmask, q))
        return 1 + best

    if n == 0:
        return 0
    return max(dp(1, full, p) for p in range(n))

def check_reselection_bound(max_group_size=7, max_child_homes=4):
    checked = 0
    worst_slack = None
    tight_examples = []
    for n in range(1, max_group_size + 1):
        for H in range(1, max_child_homes + 1):
            for homes in product(range(H + 1), repeat=n):
                used = set(homes)
                if not any(h > 0 for h in used):
                    continue
                actual = max_reselections_for_home_partition(homes)
                represented = len(used)
                bound = represented - 1
                checked += 1
                if actual > bound:
                    return False, checked, {
                        "n": n, "homes": homes,
                        "actual": actual, "bound": bound,
                    }
                slack = bound - actual
                if worst_slack is None or slack > worst_slack[0]:
                    worst_slack = (slack, homes, actual, bound)
                if actual == bound and len(tight_examples) < 8:
                    tight_examples.append((homes, actual, bound))
    return True, checked, {
        "tight_examples": tight_examples,
        "largest_observed_slack": worst_slack,
    }

def exponent_table():
    rows = []
    for alpha in [0.50, 0.60, 0.70, 0.75, 0.80, 0.90]:
        old = (2 + alpha) / 3
        new = (1 + alpha) / 2
        rows.append((alpha, old, new, old-new))
    return rows

def main():
    ok1, n1, info1 = check_reselection_bound()
    ok2, n2, info2 = check_tree_colour_bound(max_n=7, max_colors=3)

    print("C-HD re-selection refinement sanity checks")
    print("=" * 48)
    print(f"Reselection/home bound: {'PASS' if ok1 else 'FAIL'} ({n1:,} cases)")
    if not ok1:
        print("Counterexample:", info1)
        raise SystemExit(1)

    print(f"Tree colour/bichromatic bound: {'PASS' if ok2 else 'FAIL'} ({n2:,} cases)")
    if not ok2:
        print("Counterexample:", info2)
        raise SystemExit(1)

    print("\nTight reselection examples (homes, actual, colours-1):")
    for ex in info1["tight_examples"]:
        print(" ", ex)

    print("\nConditional exponent table for m = n log^alpha n")
    print(" alpha    old C-HD    proposed    improvement")
    for a, old, new, delta in exponent_table():
        print(f" {a:5.2f}    {old:8.5f}    {new:8.5f}    {delta:10.5f}")

    print("\nAt alpha=3/4:")
    print(" old:      n log^(11/12) n")
    print(" proposed: n log^(7/8) n")

if __name__ == "__main__":
    main()
