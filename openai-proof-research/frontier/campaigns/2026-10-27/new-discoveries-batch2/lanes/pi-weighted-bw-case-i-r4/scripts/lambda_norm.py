import numpy as np
from fractions import Fraction as F

def Lambda_full_norm2(w):
    n = len(w); idx = lambda i,j: i*n+j
    pairs = [(a,b) for a in range(n*n) for b in range(a+1,n*n)]
    N = len(pairs); M = np.zeros((n*n, N))
    for ci,(a,b) in enumerate(pairs):
        ai,aj = divmod(a,n); bi,bj = divmod(b,n)
        if aj==bi: M[idx(ai,bj),ci] += w[aj]      # e_(ik)^(kj) -> +w_k e_ij
        if bj==ai: M[idx(bi,aj),ci] -= w[bj]      # e_(kj)^(ik) -> -w_k e_ji? careful: (b,a)=((k,j),(i,k)) maps to e_(j,i)... 
    return np.linalg.eigvalsh(M.T@M)[-1]

# exact rational weights
for n in [3,4,5]:
    w = [F(9,1),F(4,1),F(1,1)][:n] if n==3 else [F(9),F(4),F(2),F(1)][:n]
    wn = np.array([float(x) for x in w])
    lam2 = Lambda_full_norm2(wn)
    c2 = float(w[0]**2+w[1]**2)
    print(f"n={n} w={w}: ||L||^2={lam2:.6f} c^2={c2:.6f} ratio={lam2/c2:.6f}")
