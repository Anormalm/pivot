#!/usr/bin/env python3
"""
Exhaustive sanity check for the refined C-HD full-call home-colour charge.

For a parent-first tree piece T, assign each vertex a home:
  0   = parent-own/final W' home (corresponds to Option.none)
  >0  = a child home (corresponds to Option.some Y)

For every nonempty pivot-group subset P of T, check:

  child_homes(P) + own_indicator(P)
      = distinct_homes(P)

and

  distinct_homes(P) - 1
      <= bichromatic_parent_edges(T).

The second inequality follows from the existing upstream tree-colour lemma
applied to the containing piece. This script is only a finite independent
falsification test of the refined `mkOf + ownGroupsOf` idea.
"""

from itertools import product
import argparse
import json
from pathlib import Path

def all_parent_arrays(n):
    if n == 1:
        yield (-1,)
        return
    choices = [range(v) for v in range(1, n)]
    for ps in product(*choices):
        yield (-1,) + tuple(ps)

def bichromatic_edges(parent, homes):
    return sum(
        1 for v in range(1, len(parent))
        if homes[v] != homes[parent[v]]
    )

def run(max_n=6, num_homes=3):
    checked = 0
    equality_checked = 0

    for n in range(1, max_n + 1):
        for parent in all_parent_arrays(n):
            for homes in product(range(num_homes), repeat=n):
                bich = bichromatic_edges(parent, homes)

                for mask in range(1, 1 << n):
                    represented = {
                        homes[v] for v in range(n)
                        if (mask >> v) & 1
                    }
                    child_homes = sum(h > 0 for h in represented)
                    own = int(0 in represented)
                    distinct = len(represented)

                    equality_checked += 1
                    if child_homes + own != distinct:
                        return {
                            "violations": 1,
                            "kind": "home_count_identity",
                            "n": n,
                            "parent": parent,
                            "homes": homes,
                            "mask": mask,
                        }

                    checked += 1
                    if distinct - 1 > bich:
                        return {
                            "violations": 1,
                            "kind": "bichromatic_bound",
                            "n": n,
                            "parent": parent,
                            "homes": homes,
                            "mask": mask,
                            "distinct_homes": distinct,
                            "bichromatic_edges": bich,
                        }

    return {
        "max_n": max_n,
        "num_homes": num_homes,
        "group_subsets_checked": checked,
        "home_identity_checks": equality_checked,
        "violations": 0,
        "checked_inequalities": [
            "child_homes(P) + own_indicator(P) == distinct_homes(P)",
            "distinct_homes(P) - 1 <= bichromatic_parent_edges(containing_piece)",
        ],
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--max-n", type=int, default=6)
    ap.add_argument("--num-homes", type=int, default=3)
    ap.add_argument(
        "--summary",
        type=Path,
        default=Path("results/own_home_colour_summary.json"),
    )
    args = ap.parse_args()
    summary = run(args.max_n, args.num_homes)
    args.summary.parent.mkdir(parents=True, exist_ok=True)
    args.summary.write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))
    if summary["violations"]:
        raise SystemExit(1)

if __name__ == "__main__":
    main()
