#!/usr/bin/env python3
"""Abstract invalidation stress test for version-tagged FindPivots scan caches.

This intentionally models the minimum information guaranteed by a version
cache: a strict tail-label decrease invalidates the old scan result, so the
old relevant prefix may have to be replayed.

It is not a graph-realizability proof. Its purpose is to show that version
tags alone cannot imply a subquadratic worst-case bound.
"""
import csv
from pathlib import Path

def rows():
    out=[]
    for k in [8,16,32,64,128,256]:
        q=k
        r=k
        baseline=q*r
        unchanged_version_cache=r
        adversarial_version_cache=q*r
        out.append({
            "k":k,
            "extractions_q":q,
            "relevant_edges_r":r,
            "baseline_scans":baseline,
            "cache_if_version_stable":unchanged_version_cache,
            "cache_with_change_before_each_extraction":adversarial_version_cache,
            "stable_improvement_factor":baseline/unchanged_version_cache,
            "adversarial_improvement_factor":baseline/adversarial_version_cache,
        })
    return out

if __name__ == "__main__":
    data=rows()
    p=Path("results/version_cache_invalidation.csv")
    p.parent.mkdir(parents=True,exist_ok=True)
    with p.open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=data[0].keys())
        w.writeheader(); w.writerows(data)
    for r in data:
        print(r)
