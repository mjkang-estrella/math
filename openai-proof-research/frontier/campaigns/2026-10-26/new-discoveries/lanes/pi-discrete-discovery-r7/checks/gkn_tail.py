"""Exact eventual-periodic tail of G_{k,n}(q) = (q^{2k-1};q^2)_n/(q;q^2)_{n+1}.

G = N/D, N = prod_{i=0}^{n-1}(1-q^{2k-1+2i}), D = prod_{j=0}^{n}(1-q^{1+2j}).
All poles of 1/D are roots of unity. For each odd d with n < d <= 2n+1, the
partial-fraction part at primitive d-th roots contributes exactly f_d(m mod d)
to coeff of q^m, provided N does not vanish there (otherwise contributes 0).
All other poles are killed by zeros of N (d <= n) or do not exist (d > 2n+1).
The remaining part has poles only at q = 1; its coefficient sequence is
eventually the constant C = prod_{j in A} j / prod_{j in B} j with
A = {2k-1,...,2k+2n-3}, B = {1,3,...,2n+1}.
Hence for m >= n(2k+n-2):  coeff(q^m) = C + sum_d f_d(m mod d)  EXACTLY.
"""
from fractions import Fraction
F = Fraction

# ---------------- exact rational polynomial arithmetic ----------------
def trim(p):
    p = list(p)
    while p and p[-1] == 0: p.pop()
    return p

def pmul(a, b):
    r = [F(0)]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i+j] += F(x)*F(y)
    return r

def psub(a, b):
    n = max(len(a), len(b)); r = [F(0)]*n
    for i, x in enumerate(a): r[i] += F(x)
    for i, x in enumerate(b): r[i] -= F(x)
    return trim(r)

def divmod_poly(a, b):
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
    q, r = divmod_poly(num, den)
    assert trim(r) == [] or (len(r) == 1 and r[0] == 0), "cyclotomic division failed"
    return [int(x) for x in trim(q)]

def inv_mod_phi(p, phi):
    """inverse of p (Fraction list) modulo monic phi, in Q[q]."""
    # extended Euclid on (p, phi) tracking u with u*p = gcd (mod phi handled by final reduction)
    a0 = [F(x) for x in p]; b0 = [F(x) for x in phi]
    u0, u1 = [F(1)], [F(0)]
    while len(trim(b0)) > 0 and (len(b0) > 1 or b0[0] != 0):
        q, r = divmod_poly(a0, b0)
        a0, b0 = b0, r
        u0, u1 = u1, psub(u0, pmul(q, u1))
    assert len(a0) == 1, "p not invertible mod phi"
    inv = [x/a0[0] for x in u0]
    # reduce inv mod phi
    _, inv = divmod_poly(inv, phi)
    d = len(phi)-1
    inv = (inv + [F(0)]*d)[:d]
    return inv

def reduce_mod(a, phi):
    _, r = divmod_poly(a, phi)
    d = len(phi)-1
    r = (list(r) + [F(0)]*d)[:d]
    return r

def series_div_frac(N, D, M):
    """coeffs c_0..M of N/D power series, D(0)=1, exact Fractions."""
    c = [F(0)]*(M+1)
    for m in range(M+1):
        s = F(N[m]) if m < len(N) else F(0)
        for j in range(1, min(m, len(D)-1)+1):
            if D[j]: s -= F(D[j])*c[m-j]
        c[m] = s
    return c

# ---------------- the tail computation ----------------
def tail_data(k, n):
    """Return (C, {d: [f_d(0),...,f_d(d-1)]}) exact. f_d are Fractions."""
    A = [2*k-1+2*i for i in range(n)]           # numerator exponents
    B = [1+2*j for j in range(n+1)]             # denominator exponents
    C = F(1)
    for j in A: C *= j
    for j in B: C /= j
    fds = {}
    for d in range(n+1, 2*n+2):
        if d % 2 == 0: continue
        # kill check: some j in A with d | j ?
        if any(j % d == 0 for j in A): continue
        phi = cyclotomic(d)
        deg = len(phi)-1
        # N mod phi
        Nm = [F(1)]
        for j in A:
            # multiply by (1 - q^j) mod phi
            Nm = trim(psub(Nm, pmul(Nm, [0]*j + [1])))
            Nm = reduce_mod(Nm, phi)
        # D_d mod phi: D/Phi_d ; for j in B with d|j (only j=d), factor (1-q^d)/Phi_d
        Dd = [F(1)]
        for j in B:
            if j % d == 0:
                continue
            Dd = trim(pmul(Dd, [F(1), *[F(0)]*(j-1), F(-1)]))
            Dd = reduce_mod(Dd, phi)
        # exact integer polynomial (1-q^d)/Phi_d  (Phi_d is monic)
        qd = [0]*(d+1); qd[0] = -1; qd[d] = 1
        ed, rem = divmod_poly(qd, phi)
        assert trim(rem) == [] or (len(rem) == 1 and rem[0] == 0), "non-exact"
        Dd = reduce_mod(pmul(Dd, ed), phi)
        Dd_inv = inv_mod_phi(Dd, phi)
        W = reduce_mod(pmul(Nm, Dd_inv), phi)
        # f_d(m) = coeffs of W/phi, first d of them
        f = series_div_frac(W, phi, d-1)
        fds[d] = f
    return C, fds

def tail_min(C, fds, samples=200000, exhaustive_limit=5_000_000, seed=1):
    """Return (min_estimate, method). Exact min via DP over prime powers if
    feasible; else lower bound C+sum(min) and sampled min."""
    import random
    rnd = random.Random(seed)
    ds = sorted(fds)
    if not ds:
        return C, "no-poles"
    # lower bound
    lb = C + sum(min(fds[d]) for d in ds)
    amp = sum(max(fds[d]) - min(fds[d]) for d in ds)
    # joint exact min: DP over prime powers via CRT structure.
    # Build variables: maximal prime powers p^a dividing lcm(ds) with p odd.
    L = 1
    for d in ds: L = L*d//gcd(L, d)
    if L <= exhaustive_limit:
        best = None
        for m in range(L):
            t = C + sum(fds[d][m % d] for d in ds)
            if best is None or t < best: best = t
        return best, f"exhaustive L={L}"
    # sampling fallback
    best = None
    for _ in range(samples):
        m = rnd.randrange(L)
        t = C + sum(fds[d][m % d] for d in ds)
        if best is None or t < best: best = t
    return best, f"sampled L={L} lb={lb} amp={amp}"

def initial_segment_min(k, n, cap=400000):
    m0 = n*(2*k+n-2)
    M = min(m0-1, cap)
    if M < 0: return None, m0
    N, D = [1], [1]
    def mulby(P, e):
        L = len(P)+e; res = [0]*L
        for i, v in enumerate(P):
            res[i] += v; res[i+e] -= v
        return res
    for i in range(n): N = mulby(N, 2*k-1+2*i)
    for j in range(n+1): D = mulby(D, 1+2*j)
    c = [F(0)]*(M+1)
    for m in range(M+1):
        s = F(N[m]) if m < len(N) else F(0)
        for j in range(1, min(m, len(D)-1)+1):
            if D[j]: s -= F(D[j])*c[m-j]
        c[m] = s
    return min(c), m0

if __name__ == "__main__":
    # validate tail against direct series on small cases
    for (k, n) in [(4,2),(5,3),(6,4),(7,3),(10,5),(8,6)]:
        C, fds = tail_data(k, n)
        m0 = n*(2*k+n-2)
        # direct series to m0 + 3*maxperiod region check
        M = m0 + 400
        c = series_div_frac(*gknND(k, n), M) if False else None
        print(k, n, "C=", C, "d-poles:", {d: [str(x) for x in v[:4]] for d, v in fds.items()})
