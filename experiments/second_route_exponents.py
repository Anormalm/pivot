#!/usr/bin/env python3
"""Exponent bookkeeping for the second C-HD improvement route."""

def rows():
    for i in range(50, 76, 5):
        alpha = i / 100
        old = (2 + alpha) / 3
        new = (1 + alpha) / 2
        yield alpha, old, new, old - new

if __name__ == "__main__":
    print("alpha,current_C_HD,new_power,power_gap,A(k)=O(log k)_extra")
    for alpha, old, new, gap in rows():
        print(f"{alpha:.2f},{old:.8f},{new:.8f},{gap:.8f},loglog(n)")