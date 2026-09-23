#!/usr/bin/env python3
"""Symbolic exponent audit for the candidate C-HD parameter retuning."""

import csv, json
from pathlib import Path

TERMS = {
    "N_logN_over_t": lambda a: (1 + a) / 2,
    "m_t": lambda a: (1 + a) / 2,
    "N_L_constant_k": lambda a: (1 + a) / 2,
    "N_logN_over_t2_failed_Q": lambda a: a,
    "k2_m": lambda a: a,
    "N_t_A_M_extra": lambda a: (1 - a) / 2,
    "m_log_delta": lambda a: a,
    "m_log_tdelta": lambda a: a,
    "m_input": lambda a: a,
    "N": lambda a: 0.0,
}
LOGLOG = {"m_log_delta", "m_log_tdelta"}

def audit(alphas=None):
    if alphas is None:
        alphas = [i / 100 for i in range(0, 76, 5)]
    rows = []
    for a in alphas:
        candidate = (1 + a) / 2
        for name, fn in TERMS.items():
            exp = fn(a)
            rows.append({
                "alpha": a,
                "term": name,
                "log_exponent": exp,
                "candidate_exponent": candidate,
                "exponent_gap_candidate_minus_term": candidate - exp,
                "extra_loglog_factor": name in LOGLOG,
                "strictly_lower_power": exp < candidate - 1e-12,
                "same_power": abs(exp - candidate) <= 1e-12,
            })
    return rows

if __name__ == '__main__':
    rows = audit()
    out = Path('results/master_term_exponents.csv')
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open('w', newline='') as f:
        w = csv.DictWriter(f, fieldnames=rows[0].keys())
        w.writeheader()
        w.writerows(rows)
    bad = [r for r in rows if r['log_exponent'] > r['candidate_exponent'] + 1e-12]
    summary = {
        'alpha_range': [0.0, 0.75],
        'rows': len(rows),
        'terms_exceeding_candidate_power': len(bad),
        'same_power_terms': sorted(set(r['term'] for r in rows if r['same_power'])),
        'note': ('m_log_delta and m_log_tdelta carry O(log log n) factors but '
                 'their log-power alpha is strictly below (1+alpha)/2 for alpha<1.'),
    }
    Path('results/master_term_summary.json').write_text(json.dumps(summary, indent=2))
    print(json.dumps(summary, indent=2))