"""Exact tail structure of G_{k,n}(q) = (q^{2k-1};q^2)_n/(q;q^2)_{n+1}.

Reuses r7 lane's exact cyclotomic machinery (read-only import).
New here: per-pole-order analysis of f_c and a pure-Ramanujan test.

f_c(r) := sum over primitive zeta of order c of beta_zeta * zeta^{-r},
with beta_zeta the residue of G at zeta in the 1/(1-q/zeta) convention.

Pure-Ramanujan hypothesis: exists rational K>0 and integer w with
    f_c(r) = -K * c_c(r - w)   for all r,
where c_c(j) = Ramanujan sum.
"""
import sys
sys.path.insert(0, '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/pi-discrete-discovery-r7/checks')
from gkn_tail2 import tail_components, contrib_series
from fractions import Fraction as F
from math import gcd

def mu(n):
    if n == 1: return 1
    cnt = 0; m = n; p = 2
    while p*p <= m:
        if m % p == 0:
            m //= p
            if m % p == 0: return 0
            cnt += 1
        p += 1
    if m > 1: cnt += 1
    return -1 if cnt % 2 else 1

def phi_euler(n):
    r = n; m = n; p = 2
    while p*p <= m:
        if m % p == 0:
            while m % p == 0: m //= p
            r -= r//p
        p += 1
    if m > 1: r -= r//m
    return r

def ramanujan(c, j):
    d = gcd(j, c)
    return mu(c//d)*phi_euler(c)//phi_euler(c//d)

def analyze(k, n, verbose=True):
    C, comps = tail_components(k, n)
    out = {"C": C, "poles": []}
    for (c, s, bs, phi) in comps:
        assert s == 1, f"unexpected pole order {s} at c={c} for (k,n)=({k},{n})"
        fs = contrib_series(c, s, bs, phi, c-1)  # f_c(0..c-1) exact
        # test pure Ramanujan: f_c(r) = -K c_c(r-w)
        best = None
        for w in range(c):
            denom = [ramanujan(c, (r - w) % c) for r in range(c)]
            for r0 in range(c):
                if denom[r0] != 0:
                    K = -fs[r0]/F(denom[r0])
                    ok = all((fs[r] == -K*F(denom[r])) for r in range(c))
                    if ok:
                        best = (K, w)
                        break
            if best: break
        out["poles"].append((c, fs, best))
        if verbose:
            print(f"  c={c}: f={[str(x) for x in fs]}  ramanujan_fit={best}")
    return out

if __name__ == "__main__":
    for (k, n) in [(3,1),(3,2),(4,2),(5,3),(6,4),(4,5),(7,3),(5,8),(10,5),(8,6),(6,2),(4,3)]:
        print(f"(k,n)=({k},{n})  C={tail_components(k,n)[0]}")
        analyze(k, n)
        print()
