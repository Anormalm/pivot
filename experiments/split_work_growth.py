#!/usr/bin/env python3
"""Idealized lower-envelope for work spent splitting one oversized lazy block."""

import csv
import json
from pathlib import Path

def split_work(s, M):
    # Best-case balanced median splitting. Count only one linear scan per
    # split and stop once blocks are at most 2M+1.
    if s <= 2 * M + 1:
        return 0
    a = s // 2
    b = s - a
    return s + split_work(a, M) + split_work(b, M)

def run(M=64, max_log_ratio=12):
    rows = []
    for r in range(max_log_ratio + 1):
        ratio = 2 ** r
        s = M * ratio
        work = split_work(s, M)
        rows.append({
            "M": M,
            "ratio_s_over_M": ratio,
            "log2_ratio": r,
            "entries": s,
            "ideal_split_scan_work": work,
            "work_per_entry": work / s,
        })
    return rows

if __name__ == "__main__":
    rows = run()
    out = Path("results/split_work_growth.csv")
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=rows[0].keys())
        w.writeheader()
        w.writerows(rows)
    summary = {
        "M": rows[0]["M"],
        "work_per_entry_at_ratio_1": rows[0]["work_per_entry"],
        "work_per_entry_at_ratio_4096": rows[-1]["work_per_entry"],
        "observation": "Even with perfectly balanced median splits and counting only one linear scan per split, exhausting an oversized block costs Theta(p log(p/M)) total split-scan work."
    }
    Path("results/split_work_growth_summary.json").write_text(
        json.dumps(summary, indent=2)
    )
    print(json.dumps(summary, indent=2))
