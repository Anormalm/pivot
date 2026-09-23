#!/usr/bin/env python3
"""
Exhaustively check the exact adversarial re-selection count for one pivot
group under the relaxed home model.

home 0: parent-own/final region
home h>0: child-return region h, processed in increasing h

After a re-selection we allow an adversary to choose ANY residual pivot.
This is more permissive than C-HD's minimum-label pivot rule.

Exact formula checked:

    max_reselections =
        #positive child homes                     if home 0 is present
        max(0, #positive child homes - 1)         otherwise

Equivalently, whenever the group is nonempty,

    max_reselections = #represented homes - 1.
"""

from functools import lru_cache
from itertools import product
import argparse
import json
from pathlib import Path

def max_reselections(homes):
    n = len(homes)
    H = max(homes, default=0)
    full = (1 << n) - 1

    @lru_cache(None)
    def dp(i, mask, pivot):
        if i > H or mask == 0:
            return 0

        removed = 0
        for v, h in enumerate(homes):
            if h == i and ((mask >> v) & 1):
                removed |= 1 << v
        newmask = mask & ~removed

        if not ((removed >> pivot) & 1):
            return dp(i + 1, newmask, pivot) if newmask else 0

        if newmask == 0:
            return 0

        return 1 + max(
            dp(i + 1, newmask, q)
            for q in range(n)
            if (newmask >> q) & 1
        )

    if n == 0:
        return 0
    return max(dp(1, full, p) for p in range(n))

def exact_formula(homes):
    child_homes = {h for h in homes if h > 0}
    if 0 in homes:
        return len(child_homes)
    return max(0, len(child_homes) - 1)

def run(max_group_size=8, max_child_home_labels=4):
    checked = 0
    by_n = {}

    for n in range(1, max_group_size + 1):
        count_n = 0
        for H in range(1, max_child_home_labels + 1):
            for homes in product(range(H + 1), repeat=n):
                if not any(h > 0 for h in homes):
                    continue

                actual = max_reselections(homes)
                predicted = exact_formula(homes)
                checked += 1
                count_n += 1

                if actual != predicted:
                    return {
                        "max_group_size": max_group_size,
                        "max_child_home_labels": max_child_home_labels,
                        "states_checked": checked,
                        "violations": 1,
                        "counterexample": {
                            "n": n,
                            "H": H,
                            "homes": homes,
                            "actual": actual,
                            "predicted": predicted,
                        },
                    }

        by_n[n] = count_n

    return {
        "max_group_size": max_group_size,
        "max_child_home_labels": max_child_home_labels,
        "states_checked": checked,
        "violations": 0,
        "formula": (
            "max reselections = #child homes if own-home present, "
            "else max(0,#child homes-1)"
        ),
        "states_by_group_size": by_n,
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-group-size", type=int, default=8)
    ap.add_argument("--max-child-homes", type=int, default=4)
    ap.add_argument(
        "--summary",
        type=Path,
        default=Path("results/exact_characterization_summary.json"),
    )
    args = ap.parse_args()

    summary = run(args.max_group_size, args.max_child_homes)
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))

    if summary["violations"]:
        raise SystemExit(1)

if __name__ == "__main__":
    main()
