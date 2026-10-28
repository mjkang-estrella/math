"""Exact machinery for q-metallic Hankel determinants (Han-Pedon).

All arithmetic exact over Q. Polynomials: list of Fraction, index = degree,
trailing zeros trimmed. Power series: list of Fraction truncated at N.

Sources (read 2026-10-28):
- arXiv:2610.36132v1 (eq. 2.13, Lemma 2.6, Prop 2.7, Algorithm 2.3, Thm 2.2)
- arXiv:2502.05993v2 (Conjecture E, Thm F)
"""
from fractions import Fraction as Fr
import math

# ---------------- polynomial ops ----------------

def ptrim(p):
    q = list(p)
    while q and q[-1] == 0:
        q.pop()
    return q

def pmul(p, q):
    if not p or not q:
        return []
    r = [Fr(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                if b:
                    r[i + j] += a * b
    return ptrim(r)

def padd(p, q):
    n = max(len(p), len(q))
    r = [Fr(0)] * n
    for i, a in enumerate(p):
        r[i] += a
    for i, b in enumerate(q):
        r[i] += b
    return ptrim(r)

def pscale(p, c):
    return ptrim([a * c for a in p])

def pval(p):
    for i, a in enumerate(p):
        if a != 0:
            return i
    return None  # zero polynomial

def pdiv_q(p, s):
    """exact division by q^s; asserts divisibility"""
    assert p[0:s] == [0] * s if len(p) >= s else all(c == 0 for c in p)
    return ptrim(p[s:])

# ---------------- power series ops (truncated) ----------------

def sinv(p, N):
    """inverse of series p (p[0]!=0) mod q^N"""
    r = [Fr(0)] * N
    r[0] = 1 / p[0]
    for i in range(1, N):
        s = Fr(0)
        for j in range(1, i + 1):
            if j < len(p) and p[j] != 0:
                s += p[j] * r[i - j]
        r[i] = -s / p[0]
    return r

def smul(p, q, N):
    r = [Fr(0)] * N
    for i, a in enumerate(p):
        if a == 0:
            continue
        for j, b in enumerate(q):
            if b == 0:
                continue
            if i + j < N:
                r[i + j] += a * b
    return r

def struncate(p, N):
    return list(p[:N]) + [Fr(0)] * max(0, N - len(p))

# ---------------- coefficients of Phi_n ----------------

def phi_coeffs(n, N):
    """coefficients f_0..f_{N-1} of Phi_n from eq (2.13):
    q Phi^2 + B Phi - 1 = 0, B = (1+q^n)(1-q) - q[n]_q.
    i>=1: f_i = -sum_{a=1}^{i} B_a f_{i-a} - (F^2)_{i-1}
    (B_a for a>n+1 is 0; A = -1 contributes only at i=0)"""
    # B_a
    B = [Fr(0)] * (n + 2)
    # (1+q^n)(1-q) = 1 - q + q^n - q^{n+1}; minus (q + ... + q^n)
    for a in range(1, n + 2):
        c = Fr(0)
        # from (1+q^n)(1-q): coeff at a: -1 (a=1), +1 (a=n), -1 (a=n+1)
        if a == 1:
            c += -1
        if a == n:
            c += 1
        if a == n + 1:
            c += -1
        # from -q[n]_q: -1 at each a in 1..n
        if 1 <= a <= n:
            c += -1
        B[a] = c
    f = [Fr(0)] * N
    f[0] = Fr(1)
    for i in range(1, N):
        s = Fr(0)
        for a in range(1, min(i, n + 1) + 1):
            if B[a] != 0:
                s += B[a] * f[i - a]
        # (F^2)_{i-1}
        t = Fr(0)
        for b in range(i):
            t += f[b] * f[i - 1 - b]
        f[i] = -s - t
    return f

# ---------------- quadratic triple for shifts ----------------

def shift_triple(n, ell, N, check_N=200):
    """(A,B,C) for Phi_n^(ell), iterating Lemma 2.6 ell times from
    A0=-1, B0, C0=q, using f0=coeff kappa_i at each step.
    Requires phi_coeffs(n, ell) for the constant terms."""
    f = phi_coeffs(n, ell + 1)
    A = ptrim([Fr(-1)])
    B0 = [Fr(0)] * (n + 2)
    for a in range(n + 2):
        c = Fr(0)
        # (1+q^n)(1-q): +1 at a=0, -1 at a=1, +1 at a=n, -1 at a=n+1
        if a == 0: c += Fr(1)
        if a == 1: c += Fr(-1)
        if a == n: c += Fr(1)
        if a == n + 1: c += Fr(-1)
        # -q[n]_q: -1 at each a in 1..n
        if 1 <= a <= n: c += Fr(-1)
        B0[a] = c
    B = ptrim(B0)
    C = ptrim([Fr(0), Fr(1)])  # q
    for i in range(ell):
        f0 = f[i]  # constant term of current series Phi_n^(i)
        num = padd(padd(A, pscale(B, f0)), pscale(C, f0 * f0))
        A = pdiv_q(num, 1)
        B = padd(B, pscale(C, 2 * f0))
        C = pmul(C, [Fr(0), Fr(1)])
    # sanity: check the equation holds as series mod q^check_N
    Fall = phi_coeffs(n, ell + check_N)
    F = Fall[ell:ell + check_N]
    NN = check_N
    check = padd(padd(A, smul(B, F, NN)), smul(C, smul(F, F, NN), NN))
    assert all(c == 0 for c in check), "shift triple does not satisfy equation"
    return A, B, C

# ---------------- NextABC ----------------

def nextabc(A, B, C):
    """One step. Returns (k, a, D, A*, B*, C*)."""
    k = pval(A)
    assert k is not None, "A is zero"
    a = A[k]
    K2 = k + 2
    # D = a q^k B/A - a q^k C/B mod q^{k+2}, deg <= k+1, D(0)=1
    N = K2
    # a q^k / A = 1 / (A/(a q^k)) : series with constant term 1
    Ahat = struncate(A, N)
    Ahat[0:k + 1] = [x / a for x in A[k:k + 1]] + [x / a for x in A[k + 1:N]] \
        if False else Ahat[0:k + 1]
    # simpler: Ahat = A/a as series (val k); divide by q^k -> series const 1
    Ahat = ptrim([x / a for x in A])
    Ahatq = Ahat[k:]  # series A/(a q^k), constant term 1
    inv1 = sinv(struncate(Ahatq, N), N)  # a q^k / A
    term1 = smul(struncate(B, N), inv1, N)
    # a q^k C / B: C has valuation >= 1
    invB = sinv(struncate(B, N), N)
    term2 = smul(smul(smul(struncate(C, N), [Fr(0)] * k + [Fr(1)], N), invB, N), [Fr(a)], N)
    D = [term1[i] - (term2[i] if i < len(term2) else 0) for i in range(N)]
    # deg D <= k+1: truncate
    assert all(c == 0 for c in D[k + 2:]), "D degree too large"
    D = ptrim(D[:k + 2])
    assert D[0] == 1
    # A* = (-D^2 A/a + B D q^k - C a q^{2k}) / q^{2k+2}
    D2 = pmul(D, D)
    t1 = pscale(pmul(D2, A), Fr(1) / a)
    t2 = pmul(pmul(B, D), [Fr(0)] * k + [Fr(1)])
    t3 = pscale(pmul(C, [Fr(0)] * (2 * k) + [Fr(1)]), a)
    num = padd(padd(pscale(t1, Fr(-1)), t2), pscale(t3, Fr(-1)))
    Astar = pdiv_q(num, 2 * k + 2)
    # B* = 2 A D / (a q^k) - B
    AD = pmul(A, D)
    assert all(c == 0 for c in AD[:k]), "AD val < k"
    ADq = ptrim([x / a for x in AD[k:]])
    Bstar = ptrim(padd(pscale(ADq, Fr(2)), pscale(B, Fr(-1))))
    # C* = -A q^2 / a
    Cstar = pscale(pdiv_q(pmul(A, [Fr(0), Fr(0), Fr(1)]), 0), Fr(-1) / a)
    return k, a, D, Astar, Bstar, Cstar

def hfraction(n, ell, steps, N=400):
    """Run NextABC on Phi_n^(ell) for given number of steps.
    Returns list of (k_m, a_m) for m=1..steps and the D's."""
    A, B, C = shift_triple(n, ell, N)
    out = []
    Ds = []
    for m in range(steps):
        k, a, D, A, B, C = nextabc(A, B, C)
        out.append((k, a))
        Ds.append(D)
    return out, Ds

# ---------------- determinants from H-fraction data ----------------

def determinants(data):
    """data = [(k_m, a_m)] m=1..M  (sigma_{j}=k_{j+1}, v_j=-a_{j+1}).
    Returns dict index->value of nonzero determinants Delta_{s_j}(F),
    plus s_j list."""
    M = len(data)
    sigma = [data[j][0] for j in range(M - 1)]  # sigma_j = k_{j+1}, j=0..M-2
    v = [-data[j][1] for j in range(M - 1)]     # v_j = -a_{j+1}
    s = [0]
    for sg in sigma:
        s.append(s[-1] + sg + 1)
    # Delta_{s_j} = (-1)^{eps_j} prod_{i<j} v_i^{s_j - s_i}
    # factor v_i into primes
    def factor(fr):
        num, den = fr.numerator, fr.denominator
        fac = {}
        for x, sgn in ((num, 1), (den, -1)):
            x = abs(x)
            d = 2
            while d * d <= x:
                while x % d == 0:
                    fac[d] = fac.get(d, 0) + sgn
                    x //= d
                d += 1
            if x > 1:
                fac[x] = fac.get(x, 0) + sgn
        return fac
    vfs = [factor(x) for x in v]
    # Delta values: maintain prime exponent vector of Delta_{s_j}
    # Delta_{s_j} = prod_i v_i^{s_j - s_i}; exponent of prime p:
    #   E = sum_i e_i[p] * (s_j - s_i)
    # incremental: Delta_{s_{j+1}} = Delta_{s_j} * ? no simple telescoping;
    # use E_j = sum_{l<j} (sigma_l + 1) T_l form? that needed v=+-2^e.
    # General: E_j[p] = sum_{i<j} e_i[p]*(s_j-s_i) = s_j*sum_i e_i[p] - sum_i e_i[p]*s_i
    # maintain S1[p]=sum_i e_i[p], S2[p]=sum_i e_i[p]*s_i
    S1, S2 = {}, {}
    sign = 0  # (-1)^eps_j
    res = {}
    for j in range(len(sigma) + 1):
        # value at s_j
        val = {}
        for p in set(S1) | set(S2):
            val[p] = S1[p] * s[j] - S2[p]
        # sign: eps_j = sum_{i<j} sigma_i(sigma_i+1)/2
        # also sign from negative v_i: v_i^{s_j-s_i} sign = sign(v_i)^{s_j-s_i}
        sg = 0
        for i in range(j):
            if v[i] < 0:
                sg = (sg + (s[j] - s[i])) % 2
        eps = sum(sigma[i] * (sigma[i] + 1) // 2 for i in range(j)) % 2
        total_sign = (sg + eps) % 2
        # check integrality
        x = Fr(1)
        for p, e in val.items():
            assert e >= 0, f"negative exponent for prime {p} at j={j}"
            x *= p ** e
        if total_sign:
            x = -x
        res[s[j]] = x
        if j < len(sigma):
            ef = vfs[j]
            for p, e in ef.items():
                S1[p] = S1.get(p, 0) + e
                S2[p] = S2.get(p, 0) + e * s[j]
    return res, s
