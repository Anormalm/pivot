#!/usr/bin/env python3
"""
Audit the DLazy potential created by BM.6 when pivots are inserted into the
fresh one-block structure.

Upstream definitions:
  ell(M,i)  = Nat.log 2 (i / M)
  Ssum(M,p) = sum_{i=1}^p ell(M,i)
  bw(M,b)   = 3 + 420 * (|b|-M) + 210 * Ssum(M,|b|)
  epot(D)   = 12 * |entries(D)| / M
  potM      = potL + epot

For a fresh one-block structure with p live, non-stale entries:
  potM(p) = 3
            + 420 * max(0,p-M)
            + 210 * Ssum(M,p)
            + floor(12p/M).

The raw insertion routine is O(1) per pivot because the structure stays one
block.  This script measures the *potential created*, which is what the
amortized BMTele proof must also pay for.
"""
import argparse
import csv
import json
from pathlib import Path

def nat_log2(x: int) -> int:
    # Lean Nat.log 2 x is 0 for x=0,1 and floor(log2 x) for x>=2.
    return 0 if x <= 1 else x.bit_length() - 1

def ssum(M: int, p: int) -> int:
    # Group indices i by q=floor(i/M), avoiding a loop over all p entries.
    total = 0
    for q in range(2, p // M + 1):
        lo = q * M
        hi = min(p, (q + 1) * M - 1)
        if hi >= lo:
            total += (hi - lo + 1) * nat_log2(q)
    return total

def fresh_potential(M: int, p: int) -> int:
    return (
        3
        + 420 * max(0, p - M)
        + 210 * ssum(M, p)
        + (12 * p) // M
    )

def run(M: int = 1024, max_t: int = 16):
    rows = []
    for t in range(1, max_t + 1):
        ratio = 1 << t
        p = M * ratio
        pot = fresh_potential(M, p)
        delta = pot - 3
        rows.append({
            "t": t,
            "p_over_M": ratio,
            "M": M,
            "p": p,
            "Ssum_per_pivot": ssum(M, p) / p,
            "potential_increase": delta,
            "potential_increase_per_pivot": delta / p,
            "potential_per_pivot_over_t": (delta / p) / t,
        })
    return rows

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--M", type=int, default=1024)
    ap.add_argument("--max-t", type=int, default=16)
    ap.add_argument("--csv", type=Path,
        default=Path("results/fresh_init_potential.csv"))
    ap.add_argument("--summary", type=Path,
        default=Path("results/fresh_init_potential_summary.json"))
    args = ap.parse_args()

    rows = run(args.M, args.max_t)
    args.csv.parent.mkdir(parents=True, exist_ok=True)
    with args.csv.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=rows[0].keys())
        w.writeheader()
        w.writerows(rows)

    summary = {
        "M": args.M,
        "max_t": args.max_t,
        "last_row": rows[-1],
        "interpretation": (
            "For p/M=2^t, the existing DLazy potential increase per pivot "
            "grows linearly in t. Raw fresh insertion is O(1), but the current "
            "amortized accounting creates Theta(t*p) potential."
        ),
    }
    args.summary.write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))

if __name__ == "__main__":
    main()
