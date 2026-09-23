#!/usr/bin/env python3
"""
Monte Carlo stress test for the proposed C-HD full-call re-selection bound.

For each trial:
  1. sample a parent-first rooted tree;
  2. sample a home/color for every tree vertex;
  3. sample a nonempty pivot group P contained in the tree piece;
  4. compute:
       - actual maximum number of expensive BM.23 re-selections
         over arbitrary pivot choices;
       - current generic charge: 1 + bichromatic_edges(piece);
       - proposed charge: bichromatic_edges(piece).

The actual re-selection model is deliberately more permissive than C-HD:
after each re-selection the next pivot may be chosen adversarially from any
remaining group member.
"""

from functools import lru_cache
import argparse
import csv
import random
from pathlib import Path

def random_parent_first_tree(n, rng):
    parent = [-1]
    for v in range(1, n):
        parent.append(rng.randrange(v))
    return parent

def bichromatic_edges(parent, colors):
    return sum(
        1 for v in range(1, len(parent))
        if colors[v] != colors[parent[v]]
    )

def max_reselections_for_group(homes):
    if not homes:
        return 0

    positives = sorted({h for h in homes if h > 0})
    ren = {h: i + 1 for i, h in enumerate(positives)}
    homes = tuple(0 if h == 0 else ren[h] for h in homes)
    H = max(homes)
    n = len(homes)
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

    return max(dp(1, full, p) for p in range(n))

def run(trials=100_000, seed=20260923, min_n=4, max_n=24, max_homes=8):
    rng = random.Random(seed)
    rows = []
    violations = 0
    current_slack = []
    proposed_slack = []
    current_ratio = []
    proposed_ratio = []
    tight_proposed = 0

    for t in range(trials):
        n = rng.randint(min_n, max_n)
        parent = random_parent_first_tree(n, rng)
        hcount = rng.randint(2, min(max_homes, n))
        colors = [rng.randrange(hcount) for _ in range(n)]
        bich = bichromatic_edges(parent, colors)

        p = min(0.95, max(0.15, rng.betavariate(2.0, 2.0)))
        group = [v for v in range(n) if rng.random() < p]
        if not group:
            group = [rng.randrange(n)]

        own_color = rng.randrange(hcount)
        child_colors = [c for c in range(hcount) if c != own_color]
        child_map = {c: i + 1 for i, c in enumerate(child_colors)}
        group_homes = [
            0 if colors[v] == own_color else child_map[colors[v]]
            for v in group
        ]

        actual = max_reselections_for_group(group_homes)
        current = 1 + bich
        proposed = bich

        if actual > proposed:
            violations += 1
            rows.append({
                "trial": t, "n": n, "group_size": len(group),
                "homes_in_group": len(set(group_homes)),
                "actual_reselections": actual,
                "bichromatic_edges": bich,
                "current_bound": current,
                "proposed_bound": proposed,
                "violation": 1,
            })
            break

        cs = current - actual
        ps = proposed - actual
        current_slack.append(cs)
        proposed_slack.append(ps)
        if actual > 0:
            current_ratio.append(current / actual)
            proposed_ratio.append(proposed / actual)
        if actual == proposed:
            tight_proposed += 1

        rows.append({
            "trial": t, "n": n, "group_size": len(group),
            "homes_in_group": len(set(group_homes)),
            "actual_reselections": actual,
            "bichromatic_edges": bich,
            "current_bound": current,
            "proposed_bound": proposed,
            "current_slack": cs,
            "proposed_slack": ps,
            "violation": 0,
        })

    summary = {
        "seed": seed,
        "requested_trials": trials,
        "completed_trials": len(rows),
        "violations": violations,
        "max_n": max_n,
        "max_homes": max_homes,
        "mean_current_slack": sum(current_slack)/len(current_slack) if current_slack else None,
        "mean_proposed_slack": sum(proposed_slack)/len(proposed_slack) if proposed_slack else None,
        "tight_proposed_fraction": tight_proposed/len(rows) if rows else None,
        "mean_current_ratio_when_actual_positive": (
            sum(current_ratio)/len(current_ratio) if current_ratio else None
        ),
        "mean_proposed_ratio_when_actual_positive": (
            sum(proposed_ratio)/len(proposed_ratio) if proposed_ratio else None
        ),
    }
    return rows, summary

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--trials", type=int, default=100000)
    ap.add_argument("--seed", type=int, default=20260923)
    ap.add_argument("--out", type=Path, default=Path("results/random_reselection.csv"))
    ap.add_argument("--summary", type=Path, default=Path("results/random_summary.json"))
    args = ap.parse_args()

    rows, summary = run(args.trials, args.seed)
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as f:
        fieldnames = sorted({k for r in rows for k in r})
        w = csv.DictWriter(f, fieldnames=fieldnames)
        w.writeheader()
        w.writerows(rows)
    args.summary.write_text(__import__("json").dumps(summary, indent=2))
    print(__import__("json").dumps(summary, indent=2))

if __name__ == "__main__":
    main()
