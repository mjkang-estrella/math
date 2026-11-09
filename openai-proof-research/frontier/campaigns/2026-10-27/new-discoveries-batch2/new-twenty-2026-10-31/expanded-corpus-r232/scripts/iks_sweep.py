"""Sweep the intended Ismail-Kim-Stanton sign rule (MathDB 353446): for K odd, gcd(a,K)=1, 1<=a<=K/2,
b_m of prod_{i<n}(1-q^{a+iK})(1-q^{K-a+iK}); write m = +-j*a mod K with 0<=j<=(K-1)/2;
predicted b_m <= 0 if j odd, b_m >= 0 if j even.  Also reports literal-statement status
(printed range 0<=l<K/2 includes j=K, i.e. residue 0, so b_0=1>0 refutes the literal text).
Usage: iks_sweep.py Kmin Kmax nmax"""
import sys, math
Kmin, Kmax, nmax = map(int, sys.argv[1:4])
tot = 0
for K in range(Kmin, Kmax + 1, 2):
    for a in range(1, K // 2 + 1):
        if math.gcd(a, K) != 1: continue
        par = {}
        for j in range(0, (K - 1) // 2 + 1):
            par[(j * a) % K] = j % 2; par[(-j * a) % K] = j % 2
        p = [1]; bad = None
        for n in range(1, nmax + 1):
            for e in (a + (n - 1) * K, K - a + (n - 1) * K):
                q = p + [0] * e
                for j in range(len(p)):
                    q[j + e] -= p[j]
                p = q
            for m, c in enumerate(p):
                if (par[m % K] == 1 and c > 0) or (par[m % K] == 0 and c < 0):
                    bad = (n, m, c); break
            tot += 1
            if bad: break
        print('K', K, 'a', a, 'checked n<=', nmax if not bad else bad[0], 'violation', bad, flush=True)
print('total (K,a,n) checked', tot)
