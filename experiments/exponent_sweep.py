#!/usr/bin/env python3
"""Print the old and candidate logarithmic exponents for m = n log^alpha n."""

def rows():
    for i in range(50, 100, 5):
        alpha = i / 100
        old = (2 + alpha) / 3
        candidate = (1 + alpha) / 2
        yield alpha, old, candidate, old - candidate

if __name__ == "__main__":
    print("alpha,old_C_HD,candidate,improvement")
    for row in rows():
        print(",".join(f"{x:.8f}" for x in row))
