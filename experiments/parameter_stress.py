#!/usr/bin/env python3
"""Stress-test the new parameter route for the recursive DLazy insertion bound."""
import argparse
import csv
import json
import math
from pathlib import Path

def make_row(q, alpha):
    x = 2.0 ** q
    d = x ** alpha
    t = max(16.0, math.ceil(math.sqrt(x / d)))
    L = math.floor(x / t) + 1.0
    delta = 5.0 * d
    pref = (3.0 * (L + 1.0) + 3.0 * delta) * 2.0 * t * t
    log2rho = math.log2(pref) + t
    log2_8rho8 = 3.0 + log2rho + math.log2(1.0 + 2.0 ** (-log2rho))
    return {
        "q_log2_lgN": q, "alpha": alpha, "lgN": x, "density": d,
        "t_new": t, "L_new": L,
        "log2_8rho_plus_8": log2_8rho8,
        "ratio_logrho_over_t": log2_8rho8 / t,
        "old_log_exponent": (2 + alpha) / 3,
        "candidate_log_exponent": (1 + alpha) / 2,
    }

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--q-min", type=int, default=8)
    ap.add_argument("--q-max", type=int, default=80)
    ap.add_argument("--q-step", type=int, default=4)
    ap.add_argument("--alphas", type=float, nargs="+",
                    default=[0.50,0.55,0.60,0.65,0.70,0.75])
    ap.add_argument("--out", type=Path, default=Path("results/parameter_stress.csv"))
    ap.add_argument("--summary", type=Path,
                    default=Path("results/parameter_stress_summary.json"))
    args = ap.parse_args()
    qs = list(range(args.q_min, args.q_max + 1, args.q_step))
    rows = [make_row(q,a) for a in args.alphas for q in qs]
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("w", newline="") as f:
        w = csv.DictWriter(f, fieldnames=rows[0].keys())
        w.writeheader(); w.writerows(rows)
    by_alpha = {}
    for a in args.alphas:
        rs = [r for r in rows if r["alpha"] == a]
        by_alpha[str(a)] = {
            "max_ratio": max(r["ratio_logrho_over_t"] for r in rs),
            "min_ratio": min(r["ratio_logrho_over_t"] for r in rs),
            "last_ratio": rs[-1]["ratio_logrho_over_t"],
        }
    summary = {
        "q_range":[args.q_min,args.q_max], "alphas":args.alphas,
        "summary_by_alpha":by_alpha,
        "global_max_ratio":max(r["ratio_logrho_over_t"] for r in rows),
    }
    args.summary.write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))

if __name__ == "__main__":
    main()
