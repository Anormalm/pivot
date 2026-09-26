#!/usr/bin/env python3
"""Dense-clique toy model for speculative collision probes.

Baseline model:
  q roots independently exhaust a dense h-vertex region with k>h, paying
  h(h-1) internal directed-edge scans per failed root.

Speculative ownership model:
  the first probe owns the h vertices while scanning the root adjacency,
  then stops on the first already-owned/internal edge. Later roots already
  owned by that component require no independent probe.

This is deliberately an upper-level scan-count model, not a full C-HD
implementation.
"""

import argparse
import csv
from pathlib import Path

def row(h, q):
    k = h + 1
    baseline = q * h * (h - 1)
    # First root discovers h-1 other clique vertices, then the next extracted
    # vertex immediately sees an owned neighbor and collides.
    speculative = h
    return {
        "h": h,
        "q": q,
        "k": k,
        "baseline_edge_scans": baseline,
        "speculative_probe_scans": speculative,
        "reduction_factor": baseline / speculative,
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=Path("results/collision_probe_dense.csv"))
    args = ap.parse_args()
    rows = [row(h, min(h, q)) for h in [8,16,32,64,128] for q in [8,16,32,64,128]]
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=rows[0].keys())
        w.writeheader()
        w.writerows(rows)
    for r in rows:
        print(r)

if __name__ == "__main__":
    main()