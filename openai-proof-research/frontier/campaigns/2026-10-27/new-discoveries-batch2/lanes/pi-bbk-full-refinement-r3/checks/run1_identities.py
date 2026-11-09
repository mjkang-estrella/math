"""Exact structural checks, memory-bounded. Run 1: identities + simple-pole lemma."""
import sys, math
from fractions import Fraction
sys.path.insert(0, '.')
from gkn_core import G_coeffs, G_canonical_coeffs, series_mul, q_pochhammer_odd

# 1. Symmetry G_{k,n} = G_{n+2,k-2} (source Lemma 5.3 shape) and canonical reduction.
def check_identities(kmax=10, nmax=8, N=300):
    bad = []
    for k in range(2, kmax+1):
        for n in range(0, nmax+1):
            a = G_coeffs(k, n, N)
            if a != G_canonical_coeffs(k, n, N):
                bad.append(('canonical', k, n))
            if a != G_coeffs(n+2, k-2, N):
                bad.append(('symmetry', k, n))
    return bad

# 2. Simple-pole lemma: e_c := #{j in A : c | j} - #{j in B : c | j} in {-1,0,1}
#    where (reduced, M>=m form) A = odds in [2M+1, 2M+2m-3], B = odds in [1, 2m-1].
#    Re-derived directly for the canonical form: A = {2n+3+2i}, i<k-2 ; B = {1..2k-3 odd}.
def pole_orders(k, n):
    A = [2*n+3+2*i for i in range(k-2)]
    B = [2*j+1 for j in range(k-1)]
    out = {}
    for c in range(3, 2*max(n+2, k)+2, 2):
        ea = sum(1 for a in A if a % c == 0)
        eb = sum(1 for b in B if b % c == 0)
        out[c] = eb - ea   # >0 means pole of that order at primitive c-th roots
    return out

def check_simple_poles(kmax=40, nmax=40):
    worst = {}
    for k in range(2, kmax+1):
        for n in range(0, nmax+1):
            po = pole_orders(k, n)
            for c, e in po.items():
                if e > worst.get('max', -10): worst['max'] = e; worst['at'] = (k,n,c)
                if e < -1: worst.setdefault('below-1', []).append((k,n,c,e))
    return worst

if __name__ == '__main__':
    print("identities:", check_identities() or "ALL PASS")
    print("simple-pole scan:", check_simple_poles())
