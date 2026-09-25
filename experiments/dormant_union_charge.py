#!/usr/bin/env python3
"""Abstract component-merge accounting for dormant FindPivots.

This script isolates only the ownership-movement part of union-by-size.
It does NOT model label propagation and therefore is not evidence for the
full algorithmic bound.

For repeated merges of sub-k components, charge every vertex in the smaller
component once.  Each charged vertex moves into a component at least twice as
large, so total movement is O(n log k).
"""
import argparse
import csv
import heapq
from pathlib import Path

def worst_small_to_large(n: int, k: int):
    # Use a min-heap of component sizes. Repeatedly merge two smallest
    # components while the sum stays below k; when it reaches k, freeze it.
    heap=[1]*n
    heapq.heapify(heap)
    moved=0
    merges=0
    frozen=[]
    while len(heap) >= 2:
        a=heapq.heappop(heap)
        b=heapq.heappop(heap)
        if a+b >= k:
            moved += min(a,b)
            merges += 1
            frozen.append(a+b)
            continue
        moved += min(a,b)
        merges += 1
        heapq.heappush(heap,a+b)
    frozen.extend(heap)
    return {
        "n_vertices":n,
        "k":k,
        "merges":merges,
        "moved_vertex_charge":moved,
        "n_log2_k":n * max(1,(k-1).bit_length()),
        "ratio_to_nlogk":moved/(n * max(1,(k-1).bit_length())),
        "final_components":len(frozen),
    }

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--out",type=Path,
        default=Path("results/dormant_union_charge.csv"))
    args=ap.parse_args()
    rows=[]
    for k in [8,16,32,64,128,256]:
        for mult in [1,2,4,8]:
            rows.append(worst_small_to_large(mult*k,k))
    args.out.parent.mkdir(parents=True,exist_ok=True)
    with args.out.open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys())
        w.writeheader(); w.writerows(rows)
    for r in rows:
        print(r)

if __name__=="__main__":
    main()
