#!/usr/bin/env python3
"""Log-power audit for a generalized FindPivots coefficient A(k)=k^r.

Model after the N4 re-selection tightening while retaining the BM.6 t/k term:

  N*L*(k^r + t/k)
  + k^(r+1)*(m + N*L/t)
  + m*t

Set d=m/N=log^alpha n, t=log^b n, k=t (the route enabled when r≈0).
This script reports the log exponents of the resulting terms.
"""
import argparse
import csv
from pathlib import Path

def rows(alpha: float, r: float):
    # For k=t and t=log^b n.  For r=0 balance 1-b = alpha+b.
    b=(1-alpha)/2
    return [
        ("NL_A", 1-b + r*b),
        ("NL_t_over_k", 1-b),
        ("Q_m", alpha + (r+1)*b),
        ("Q_NL_over_t", 1-b + r*b),
        ("m_t", alpha+b),
    ], b

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument("--alpha",type=float,default=0.75)
    ap.add_argument("--r",type=float,default=0.0)
    ap.add_argument("--out",type=Path,default=Path("results/findpivots_generalized_balance.csv"))
    args=ap.parse_args()
    data,b=rows(args.alpha,args.r)
    args.out.parent.mkdir(parents=True,exist_ok=True)
    with args.out.open("w",newline="") as f:
        w=csv.writer(f)
        w.writerow(["term","log_exponent"])
        w.writerows(data)
    print("alpha =",args.alpha)
    print("A(k)=k^r, r =",args.r)
    print("t exponent b =",b)
    for name,e in data:
        print(f"{name:20s} {e:.8f}")
    print("max exponent =",max(e for _,e in data))

if __name__=="__main__":
    main()
