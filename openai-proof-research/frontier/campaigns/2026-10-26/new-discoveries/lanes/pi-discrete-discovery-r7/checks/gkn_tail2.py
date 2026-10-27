"""Exact tail of G_{k,n}(q) = (q^{2k-1};q^2)_n/(q;q^2)_{n+1}.

For m >= m0 = n(2k+n-2):
    coeff(q^m) = C + sum_c contrib_c(m)
where C = prod_{j in A} j / prod_{j in B} j (A = 2k-1..2k+2n-3 step2, B = 1..2n+1 step2)
and contrib_c comes from cyclotomic poles Phi_c, c odd, 3 <= c <= 2n+1, with
s = #{j in B: c|j} - #{j in A: c|j} > 0:
    contrib_c(m) = sum_{i=0}^{s-1} [q^m] b_i(q)/Phi_c(q)^{s-i},
    T = N_c * D_c^{-1} mod Phi_c^s expanded in base Phi_c: T = sum b_i Phi_c^i,
    N_c = N/Phi_c^{a}, D_c = D/Phi_c^{m} (a = #{j in A: c|j}, m = #{j in B: c|j}).
[q^m] b/Phi_c^j = sum_r (-1)^j C(r+j-1,j-1) * [q^{m-cr}] (b*E^j), E = (q^c-1)/Phi_c.
"""
from fractions import Fraction as F
from math import comb, gcd
import sys

def trim(p):
    p = list(p)
    while p and p[-1] == 0: p.pop()
    return p

def pmul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i+j] += x*y
    return r

def padd(a, b):
    n = max(len(a), len(b)); r = [0]*n
    for i, x in enumerate(a): r[i] += x
    for i, x in enumerate(b): r[i] += x
    return r

def psub(a, b):
    n = max(len(a), len(b)); r = [0]*n
    for i, x in enumerate(a): r[i] += x
    for i, x in enumerate(b): r[i] -= x
    return r

def divmod_int(a, b):
    """exact divmod of integer polys, b monic or leading any; returns (q, r) Fractions-free if exact."""
    a = [F(x) for x in a]; b = [F(x) for x in b]
    q = [F(0)]*max(1, len(a)-len(b)+1)
    while len(a) >= len(b) and trim(a):
        diff = len(a)-len(b)
        c = a[-1]/b[-1]
        q[diff] += c
        for i, x in enumerate(b):
            a[diff+i] -= c*x
        a = trim(a)
    while q and q[-1] == 0: q.pop()
    return (q or [F(0)]), (trim(a) or [F(0)])

def cyclotomic(d):
    def mu(m):
        if m == 1: return 1
        cnt = 0; mm = m; f = 2
        while mm % f == 0: cnt += 1; mm //= f
        if cnt >= 2: return 0
        for f in range(3, int(mm**0.5)+1):
            if mm % f == 0:
                c2 = 0
                while mm % f == 0: mm //= f; c2 += 1
                if c2 >= 2: return 0
                cnt += 1
        if mm > 1: cnt += 1
        return -1 if cnt % 2 else 1
    num, den = [1], [1]
    for c in range(1, d+1):
        if d % c == 0:
            e = mu(d//c)
            if e == 0: continue
            f = [0]*(c+1); f[0] = -1; f[c] = 1
            if e == 1: num = trim(pmul(num, f))
            else: den = trim(pmul(den, f))
    q, r = divmod_int(num, den)
    assert trim(r) == [] or (len(r) == 1 and r[0] == 0)
    return [int(x) for x in trim(q)]

def phi_pow(phi, e):
    r = [1]
    for _ in range(e): r = trim(pmul(r, phi))
    return r

def inv_mod_phic(p, phi):
    """inverse of p (Fraction list) modulo monic phi."""
    a0 = [F(x) for x in p]; b0 = [F(x) for x in phi]
    u0, u1 = [F(1)], [F(0)]
    while trim(b0) and (len(b0) > 1 or b0[0] != 0):
        q, r = divmod_int(a0, b0)
        a0, b0 = b0, r
        u0, u1 = u1, psub(u0, pmul(q, u1))
    assert len(a0) == 1, "not invertible mod phi"
    inv = [x/a0[0] for x in u0]
    _, inv = divmod_int(inv, phi)
    d = len(phi)-1
    return (list(inv)+[F(0)]*d)[:d]

def reduce_mod(a, phis):
    _, r = divmod_int(a, phis)
    d = len(phis)-1
    return (list(r)+[F(0)]*d)[:d]

def inv_mod_phic_power(p, phi, s):
    """inverse of p mod phi^s via Hensel lifting. p, phi int lists."""
    x = inv_mod_phic([F(v) for v in p], phi)  # mod phi
    mod = [F(v) for v in phi]
    curmod = phi[:]
    e = 1
    while e < s:
        # x' = x*(2 - p*x) mod phi^{2e}
        e2 = min(2*e, s)
        px = trim(pmul([F(v) for v in p], x))
        t = psub([F(2)], px)
        x = trim(pmul(x, t))
        x = reduce_mod(x, phi_pow(phi, e2))
        e = e2
    return x

def base_phi(T, phi, s):
    """T (Fraction list, deg < s*deg phi) -> [b_0..b_{s-1}] with T = sum b_i phi^i."""
    res = []
    cur = list(T)
    for _ in range(s):
        b, r = divmod_int(cur, phi)
        # b is quotient? no: we want cur mod phi and cur // phi
        cur = b  # quotient
        res.append(r)
    # res[i] = T div phi^i mod phi
    res = res[::-1]  # careful ordering below
    return res  # res[0] is highest? fix below

def base_phi_proper(T, phi, s):
    """returns [b_{s-1}, ..., b_0]? we return list b_0..b_{s-1}."""
    bs = []
    cur = list(T)
    for _ in range(s):
        q, r = divmod_int(cur, phi)
        bs.append(r)   # remainder = coefficient of phi^i
        cur = q
    return bs  # bs[i] = b_i

def series_div_frac(N, D, M):
    c = [F(0)]*(M+1)
    for m in range(M+1):
        s = F(N[m]) if m < len(N) else F(0)
        for j in range(1, min(m, len(D)-1)+1):
            if D[j]: s -= F(D[j])*c[m-j]
        c[m] = s
    return c

def gkn_ND(k, n):
    N, D = [1], [1]
    def mulby(P, e):
        L = len(P)+e; res = [0]*L
        for i, v in enumerate(P):
            res[i] += v; res[i+e] -= v
        return res
    for i in range(n): N = mulby(N, 2*k-1+2*i)
    for j in range(n+1): D = mulby(D, 1+2*j)
    return N, D

def tail_components(k, n):
    """Return (C, comps) where comps = list of (c, s, [b_0..b_{s-1}], phi)."""
    A = [2*k-1+2*i for i in range(n)]
    B = [1+2*j for j in range(n+1)]
    C = F(1)
    for j in A: C *= j
    for j in B: C /= j
    N, D = gkn_ND(k, n)
    comps = []
    for c in range(3, 2*n+2, 2):
        m_c = sum(1 for j in B if j % c == 0)
        a_c = sum(1 for j in A if j % c == 0)
        s = m_c - a_c
        if s <= 0: continue
        phi = cyclotomic(c)
        phim = phi_pow(phi, m_c)
        phia = phi_pow(phi, a_c)
        _, Nc = divmod_int(N, phia); assert trim(Nc) == [] or (len(Nc)==1 and Nc[0]==0) or True
        # exactness checks
        q1, r1 = divmod_int(N, phia); assert trim(r1) == [] or (len(r1)==1 and r1[0]==0), f"N not divisible phi^{a_c}"
        q2, r2 = divmod_int(D, phim); assert trim(r2) == [] or (len(r2)==1 and r2[0]==0), f"D not divisible phi^{m_c}"
        Nc = trim(q1); Dc = trim(q2)
        T = reduce_mod([F(v) for v in Nc], phi_pow(phi, s))
        Dc_inv = inv_mod_phic_power(Dc, phi, s)
        T = reduce_mod(trim(pmul(T, Dc_inv)), phi_pow(phi, s))
        bs = base_phi_proper(T, phi, s)
        comps.append((c, s, bs, phi))
    return C, comps

def contrib_series(c, s, bs, phi, M):
    """sum_i [q^m] b_i/Phi^{s-i} for m=0..M, exact Fractions."""
    tot = [F(0)]*(M+1)
    for i, b in enumerate(bs):
        j = s - i
        if not any(b): continue
        if j == 0:
            pass
        E = None
        # E = (q^c - 1)/Phi_c  exact integer poly
        qc = [0]*(c+1); qc[0] = -1; qc[c] = 1
        E, r = divmod_int(qc, phi)
        assert trim(r) == [] or (len(r) == 1 and r[0] == 0)
        # b*E^j
        BE = [F(v) for v in b]
        for _ in range(j):
            BE = trim(pmul(BE, [F(v) for v in E]))
        # [q^m] BE/(q^c-1)^j = sum_r (-1)^j C(r+j-1,j-1) BE[m-cr]
        for m in range(M+1):
            acc = F(0)
            r = 0
            while m - r*c >= 0:
                idx = m - r*c
                if idx < len(BE) and BE[idx]:
                    acc += F((-1)**j * comb(r+j-1, j-1)) * BE[idx]
                r += 1
                if r > M//c + 2: break
            tot[m] += acc
    return tot

def tail_series(k, n, M):
    """exact tail coeff estimates for m=0..M (valid m >= m0)."""
    C, comps = tail_components(k, n)
    t = [C]*(M+1)
    for (c, s, bs, phi) in comps:
        cs = contrib_series(c, s, bs, phi, M)
        for m in range(M+1): t[m] += cs[m]
    return t, C, comps
