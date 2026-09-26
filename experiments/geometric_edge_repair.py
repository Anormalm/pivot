#!/usr/bin/env python3
"""Abstract edge-rescan budget under geometric dormant-component repairs."""
import argparse
import csv
import math
from pathlib import Path

def row(k, final_size, edges):
    assert 1 <= final_size < k
    size = 1
    repairs = 0
    scans = 0
    while 2 * size <= final_size:
        size *= 2
        repairs += 1
        scans += edges
    scans += edges  # final closure repair
    logcap = max(1, math.ceil(math.log2(k)))
    return {
        "k": k,
        "final_size": final_size,
        "outgoing_edges": edges,
        "doubling_repairs": repairs,
        "total_repairs_including_final": repairs + 1,
        "full_repair_edge_scans": scans,
        "E_times_ceil_log2_k": edges * logcap,
        "ratio": scans / (edges * logcap),
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=Path("results/geometric_edge_repair.csv"))
    args = ap.parse_args()
    rows = []
    for k in [8,16,32,64,128,256,512]:
        for f in sorted(set([1,max(1,k//4),max(1,k//2),k-1])):
            for e in [f,4*f,16*f]:
                rows.append(row(k,f,e))
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=rows[0].keys())
        w.writeheader()
        w.writerows(rows)
    for r in rows:
        print(r)

if __name__ == "__main__":
    main()