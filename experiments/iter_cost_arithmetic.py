#!/usr/bin/env python3
"""Exhaustively check the one-step C-HD re-selection cost inequality."""

import json
from pathlib import Path

def run(max_g=8, max_I=12, max_marked=8, max_emptied=8, max_meeting=16):
    checked = 0
    tight = 0
    for g in range(max_g + 1):
        for I in range(max_I + 1):
            for M in range(max_marked + 1):
                for E in range(max_emptied + 1):
                    for R in range(max_meeting + 1):
                        if M + E > R:
                            continue
                        checked += 1
                        lhs = g * (M + E) + (g + 1 + I) * M + I * E
                        rhs = (2 * g + 1 + I) * R
                        if lhs > rhs:
                            return {
                                'checked_assignments': checked,
                                'violations': 1,
                                'counterexample': {'g':g,'I':I,'marked':M,'emptied':E,'meeting':R,'lhs':lhs,'rhs':rhs},
                            }
                        if lhs == rhs:
                            tight += 1
    return {
        'checked_assignments': checked,
        'violations': 0,
        'tight_assignments': tight,
        'range': {
            'g':[0,max_g], 'I':[0,max_I], 'marked':[0,max_marked],
            'emptied':[0,max_emptied], 'meeting':[0,max_meeting],
        },
        'inequality':'g(M+E)+(g+1+I)M+IE <= (2g+1+I)R under M+E<=R',
    }

if __name__ == '__main__':
    result = run()
    out = Path('results/iter_cost_arithmetic_summary.json')
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(json.dumps(result, indent=2))
    print(json.dumps(result, indent=2))
    if result['violations']:
        raise SystemExit(1)