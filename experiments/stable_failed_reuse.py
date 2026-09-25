#!/usr/bin/env python3
"""Stable failed-search reuse toy model.

This models a complete directed component of h vertices with exact labels.
All q roots lie in the component and k>h, so every local FindPivots search
fails after exploring the whole component. Failed searches are not globally
marked, so the baseline rescans the same component once per root.

This is a valid stable subclass for studying duplicate scan work. It is not
a proof that caching is sound when labels change between searches.
"""

import argparse
import csv
from pathlib import Path

def run_case(h, q, k):
    assert q <= h and k > h
    edges = h * (h - 1)
    baseline = q * edges
    cached = edges
    return {
        "h": h,
        "q": q,
        "k": k,
        "component_edges": edges,
        "baseline_edge_scans": baseline,
        "ideal_cached_edge_scans": cached,
        "scan_reduction_factor": baseline / cached,
        "duplicate_fraction": 1 - cached / baseline,
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=Path("results/stable_failed_reuse.csv"))
    args = ap.parse_args()
    rows = []
    for h in [4, 8, 16, 32, 64]:
        k = h + 1
        for q in [1, max(1, h // 4), max(1, h // 2), h]:
            rows.append(run_case(h, q, k))
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=rows[0].keys())
        w.writeheader()
        w.writerows(rows)
    print(rows[-1])

if __name__ == "__main__":
    main()