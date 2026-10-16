# Copyright (c) 2026 Myeongjin Kang. MIT License. Exploratory script; requires numpy/scipy/cvxpy; not part of verified replay.
import numpy as np, sys
from fractions import Fraction
from milp import wdisc, check

def reis_rho(k):
    # elements 1..2k+1 ; second order lists pairs (2k,2k+1),(2k-2,2k-1),...,(2,3),1  (1-indexed)
    seq = []
    for j in range(k, 0, -1):
        seq += [2 * j, 2 * j + 1]
    seq.append(1)
    return np.array(seq) - 1

for k in range(2, 9):
    N = 2 * k + 1
    w = np.ones(N)
    for i in range(1, N + 1):
        if i % 2 == 0:
            w[i - 1] = 1 - 1 / (2 * k)
    w[2 * k - 1] = 1 - 2 / (2 * k)  # element 2k
    v, eps = wdisc([np.arange(N), reis_rho(k)], w, time_limit=600)
    print(k, N, round(v, 6), "target 2-1/k =", round(2 - 1 / k, 6), "reis", round((2*k+2)/(k+2), 6), flush=True)
