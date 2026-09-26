#!/usr/bin/env python3
"""Graph-realizable batching experiment for repeated dormant-component contacts.

Family:
  q frontier roots each have one edge into v0 of a shared length-h chain.
  Root i supplies a strictly better candidate to v0 than root i-1.

Sequential eager repair:
  every better contact triggers propagation through the whole chain.

Batched contact repair:
  scan all q incoming root edges, keep only the minimum pending candidate
  for v0, then propagate through the chain once.

This is a concrete weighted-graph example showing why batching pending
decreases before reactivating a dormant component can remove a multiplicative
q factor. It does not prove that arbitrary FindPivots contacts can always be
batched this way.
"""

import argparse
import csv
from pathlib import Path

def row(q, h):
    sequential = q + q * (h - 1)
    batched = q + (h - 1)
    return {
        "q_roots": q,
        "chain_vertices": h,
        "sequential_edge_scans": sequential,
        "batched_edge_scans": batched,
        "scan_reduction_factor": sequential / batched,
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=Path("results/batched_contact_chain.csv"))
    args = ap.parse_args()
    rows = [row(q,h) for q in [8,16,32,64,128] for h in [8,16,32,64,128]]
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=rows[0].keys())
        w.writeheader()
        w.writerows(rows)
    for r in rows:
        print(r)

if __name__ == "__main__":
    main()