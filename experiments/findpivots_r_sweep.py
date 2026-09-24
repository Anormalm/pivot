#!/usr/bin/env python3
"""Optimal log exponents if FindPivots A(k)=k^r."""

import argparse
import csv
from pathlib import Path

def optimum(alpha, r):
    c = (1-alpha)/(r+2)
    b = (r+1)*(1-alpha)/(r+2)
    E = (r+1+alpha)/(r+2)
    terms = {
        "N_L_A": 1-b+r*c,
        "N_L_t_over_k": 1-c,
        "A_k_m": alpha+(r+1)*c,
        "A_k_N_L_over_t": 1-2*b+(r+1)*c,
        "m_t": alpha+b,
    }
    return b,c,E,terms

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--alpha",type=float,default=0.75)
    ap.add_argument("--out",type=Path,
        default=Path("results/findpivots_r_sweep.csv"))
    args=ap.parse_args()
    rows=[]
    for i in range(0,21):
        r=i/20
        b,c,E,terms=optimum(args.alpha,r)
        rows.append({
            "r":r,
            "alpha":args.alpha,
            "t_log_exponent_b":b,
            "k_log_exponent_c":c,
            "optimized_runtime_log_exponent":E,
            "max_checked_term":max(terms.values()),
        })
    args.out.parent.mkdir(parents=True,exist_ok=True)
    with args.out.open("w",newline="") as f:
        w=csv.DictWriter(f,fieldnames=rows[0].keys())
        w.writeheader(); w.writerows(rows)
    for row in rows:
        print(row)

if __name__=="__main__":
    main()
