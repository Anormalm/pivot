#!/usr/bin/env python3
"""Geometric rebuild accounting for dormant components.

This isolates only the replay-count consequence of a doubling-triggered
repair schedule. It does not model shortest-path correctness.
"""

import argparse
import csv
from pathlib import Path

def one(k):
    base = 1
    size = 1
    rebuild_sizes = []
    while size < k:
        size += 1
        if size >= 2 * base:
            rebuild_sizes.append(size)
            base = size
    return {
        "k": k,
        "growth_events": k - 1,
        "rebuilds": len(rebuild_sizes),
        "rebuild_sizes": ";".join(map(str, rebuild_sizes)),
        "log2_k_ceil": max(1, (k - 1).bit_length()),
        "rebuild_to_log_ratio": len(rebuild_sizes) / max(1, (k - 1).bit_length()),
    }

def failed(final_size):
    base = 1
    size = 1
    rebuild_sizes = []
    while size < final_size:
        size += 1
        if size >= 2 * base:
            rebuild_sizes.append(size)
            base = size
    if not rebuild_sizes or rebuild_sizes[-1] != size:
        rebuild_sizes.append(size)
    return {
        "final_size": final_size,
        "rebuilds_including_final": len(rebuild_sizes),
        "rebuild_sizes": ";".join(map(str, rebuild_sizes)),
        "log2_size_ceil": max(1, (final_size - 1).bit_length()),
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", type=Path, default=Path("results/geometric_repair_schedule.csv"))
    args = ap.parse_args()
    rows = [one(k) for k in [8,16,32,64,128,256,512,1024]]
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as f:
        fields = sorted({x for r in rows for x in r})
        w = csv.DictWriter(f, fieldnames=fields)
        w.writeheader(); w.writerows(rows)
    for r in rows:
        print(r)
    print("failed examples:")
    for n in [7,15,31,63,127,255]:
        print(failed(n))

if __name__ == "__main__":
    main()
