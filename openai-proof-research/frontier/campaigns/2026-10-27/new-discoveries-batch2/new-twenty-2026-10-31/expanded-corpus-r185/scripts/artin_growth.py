"""Saito growth series of the conjectured Artin-Tits presentation of HBM(e) (Alekseev-Mamedov Conj. 1.x):
m(k,k+1)=3 if e_k=e_{k+1}, infinity otherwise; m(i,j)=2 for |i-j|>=2. G(t)=1/sum_{T spherical}(-1)^{|T|} t^{len(w_T)}.
Spherical T: no adjacent pair with sign change; then W_T is a product of type-A components; len(w_0(A_m)) = m(m+1)/2.
Usage: artin_growth.py e L"""
import sys, itertools
es = sys.argv[1]; L = int(sys.argv[2]); m = len(es)
den = [0] * (L + 1)
for r in range(m + 1):
    for T in itertools.combinations(range(m), r):
        Ts = set(T); ok = True
        for k in T:
            if k + 1 in Ts and es[k] != es[k + 1]: ok = False; break
        if not ok: continue
        # components of consecutive indices
        length = 0; run = 0
        for k in range(m + 1):
            if k < m and k in Ts: run += 1
            else:
                length += run * (run + 1) // 2; run = 0
        if length <= L: den[length] += (-1) ** r
g = [0] * (L + 1); g[0] = 1
for k in range(1, L + 1):
    g[k] = -sum(den[j] * g[k - j] for j in range(1, k + 1))
print(es, g)
