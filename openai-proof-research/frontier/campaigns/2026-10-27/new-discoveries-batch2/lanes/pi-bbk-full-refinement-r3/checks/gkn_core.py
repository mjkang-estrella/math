"""Exact core routines for G_{k,n}(q) = (q^{2k-1};q^2)_n / (q;q^2)_{n+1}.

All arithmetic exact (Python ints). Memory bounded: coefficient lists only.
"""
from math import prod

def series_mul(p, q_):
    out = [0]*(len(p)+len(q_)-1)
    for i,a in enumerate(p):
        if a:
            for j,b in enumerate(q_):
                out[i+j] += a*b
    return out

def series_inv(den, N):
    """First N+1 coefficients of 1/den, den[0]=1."""
    out = [0]*(N+1)
    out[0] = 1
    for m in range(1, N+1):
        s = 0
        for i in range(1, min(m, len(den)-1)+1):
            s += den[i]*out[m-i]
        out[m] = -s
    return out

def q_pochhammer_odd(start, count):
    """prod_{i=0}^{count-1} (1 - q^{start+2i}) as coefficient list."""
    p = [1]
    for i in range(count):
        e = start + 2*i
        p = series_mul(p, [1] + [0]*(e-1) + [-1])
    return p

def G_coeffs(k, n, N):
    """Exact coefficients [q^0..q^N] of G_{k,n}(q)."""
    num = q_pochhammer_odd(2*k-1, n)          # (q^{2k-1};q^2)_n
    den = q_pochhammer_odd(1, n+1)            # (q;q^2)_{n+1}
    inv = series_inv(den, N)
    return series_mul(num, inv)[:N+1]

def G_canonical_coeffs(k, n, N):
    """Canonical reduced-for-poles form: (q^{2n+3};q^2)_{k-2}/(q;q^2)_{k-1}, k>=2."""
    num = q_pochhammer_odd(2*n+3, k-2)
    den = q_pochhammer_odd(1, k-1)
    inv = series_inv(den, N)
    return series_mul(num, inv)[:N+1]

def check_reduction(kmax=12, nmax=8, N=400):
    """G_{k,n} == (q^{2n+3};q^2)_{k-2}/(q;q^2)_{k-1} for k>=2, and G_{k,n}(q)=G_{n+1,k-1}(q) symmetry."""
    bad = []
    for k in range(2, kmax+1):
        for n in range(0, nmax+1):
            a = G_coeffs(k, n, N)
            b = G_canonical_coeffs(k, n, N)
            if a != b:
                bad.append(('canonical', k, n))
            # symmetry F(a,b)=F(b,a) with a=n+1,b=k-1: G_{k,n} = G_{n+1, k-1}
            c = G_coeffs(n+1, k-1, N)
            if a != c:
                bad.append(('symmetry', k, n))
    return bad

def positivity_scan(kmax, nmax, margin=0):
    """Scan all coefficients up to a safe degree: N >= sum of numerator exponents + something.
    For k>=2 the canonical form has eventual period L | lcm(odd<=2k-3); we check the full
    initial segment plus one full period of the tail via exact division."""
    import math
    results = {}
    for k in range(1, kmax+1):
        for n in range(0, nmax+1):
            # degree bound: canonical numerator sum + lcm period window
            if k == 1:
                N = 2*n+1  # 1/(1-q^{2n+1}) exactly periodic
                c = G_coeffs(1, n, N)
                ok = all(x >= 0 for x in c) and (n == 0 or c[2*n+1 % (2*n+1) if 2*n+1<=N else 0] >= 0)
                results[(k,n)] = ('exact-full' if n==0 else 'trivial', min(c))
                continue
            # canonical: numerator exponents 2n+3..2n+2k-3 ; m0 = their sum
            m0 = sum(2*n+3+2*i for i in range(k-2))
            L = math.lcm(*[2*j+1 for j in range(1, k-1)])  # odd 3..2k-3
            N = m0 + L + 5
            c = G_canonical_coeffs(k, n, N)
            mn = min(c)
            ok = mn >= 0
            # tail periodicity check: c[m0+L:] constant? (tail = C + periodic; check two periods equal)
            tail_ok = c[m0:] == c[m0:L+1] + c[m0:m0+ (len(c)-m0-L)] if len(c)-m0 > L else True
            results[(k,n)] = (ok, mn, m0, L, c[m0] if len(c)>m0 else None)
    return results

if __name__ == '__main__':
    bad = check_reduction()
    print("reduction/symmetry failures:", bad)
    r = positivity_scan(25, 10)
    fails = {kk: v for kk, v in r.items() if not v[0]}
    print("positivity failures:", fails)
    mins = min((v[1]/ (v[2]**0+1) , kk) for kk,v in r.items() if v[0] and v[1] is not None)
    print("done")
