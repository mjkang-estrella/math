#!/usr/bin/env python3
"""Study W_r^{(n)} := det[(B^r)_{[0,n)x[0,n)}] and its factorizations."""
import sympy as sp
from reduce import bmat_power_block, det_poly, qshift
from compute import hankel_det, pstr

q = sp.Symbol('q')

def to_sympy(a):
    return sum(c * q**e for e, c in sorted(a.items()))

def factor_str(a):
    return str(sp.factor(to_sympy(a)))

if __name__ == "__main__":
    import sys
    print("=== W_r^{(n)} = det[(B^r)_{n x n]} factored ===")
    for r in range(1, 9):
        for n in range(1, 7):
            W = det_poly(bmat_power_block(r, n))
            print(f"r={r} n={n}: {factor_str(W)}")
        print()
