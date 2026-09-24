#!/usr/bin/env python3
"""Measure C-HD's existing DLazy potential on a fresh one-block structure."""

import csv
import json
from pathlib import Path

def nat_log2(x):
    return 0 if x <= 0 else x.bit_length() - 1

def ssum(M, s):
    total = 0
    for q in range(1, s // M + 1):
        lo = q * M
        hi = min(s, (q + 1) * M - 1)
        if hi >= lo:
            total += (hi - lo + 1) * nat_log2(q)
    return total

def pot_one_block(M, s):
    # DL.bw + DL.epot, assuming all entries are live and staleCnt=0.
    bw = 3 + 420 * max(s - M, 0) + 210 * ssum(M, s)
    epot = (12 * s) // M
    return bw + epot

def run(M=64, max_log_ratio=12):
    rows = []
    for r in range(max_log_ratio + 1):
        ratio = 2 ** r
        s = M * ratio
        p = pot_one_block(M, s)
        rows.append({
            "M": M,
            "ratio_s_over_M": ratio,
            "log2_ratio": r,
            "entries": s,
            "Ssum": ssum(M, s),
            "potM_one_block": p,
            "potential_per_entry": p / s,
            "ell_at_end": nat_log2(s // M),
        })
    return rows

if __name__ == "__main__":
    rows = run()
    out = Path("results/fresh_potential_growth.csv")
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=rows[0].keys())
        w.writeheader()
        w.writerows(rows)

    summary = {
        "M": rows[0]["M"],
        "max_ratio_s_over_M": rows[-1]["ratio_s_over_M"],
        "potential_per_entry_at_ratio_1": rows[0]["potential_per_entry"],
        "potential_per_entry_at_ratio_4096": rows[-1]["potential_per_entry"],
        "ell_at_end_at_ratio_4096": rows[-1]["ell_at_end"],
        "observation": "Existing one-block potential per entry grows with log2(s/M); direct O(1) insertion is not O(1) amortized initialization under this potential."
    }
    Path("results/fresh_potential_growth_summary.json").write_text(
        json.dumps(summary, indent=2)
    )
    print(json.dumps(summary, indent=2))
