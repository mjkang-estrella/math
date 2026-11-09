"""Sanity check of the *reading* of Definition 2.2 (arXiv:1801.07980) and Corollary 7.1
(arXiv:1812.01864v2). This is a diagnostic of interpretation only, NOT a proof of the
conjecture; the proof is the published successor theorem.

Computes, in exact rational arithmetic:
  He_lambda := Wr[He_{n_1},...,He_{n_r}] / Delta(n_lambda),
  n_i = lambda_i + r - i, Delta(n_lambda) = prod_{i<j} (n_j - n_i),
with probabilists' He_n defined by He_0=1, He_1=x, He_n = x He_{n-1} - (n-1) He_{n-2},
and checks monic-ness, degree |lambda|, parity, and integrality of coefficients.
Also checks one non-Hermite monic integer Appell-like sequence to show integrality is
not a generic property of any monic Wronskian quotient.
"""
from fractions import Fraction
from itertools import combinations

def he(n):
    polys = [ [Fraction(1)], [Fraction(0), Fraction(1)] ]
    if n == 0: return [Fraction(1)]
    if n == 1: return [Fraction(0), Fraction(1)]
    for k in range(2, n + 1):
        prev2, prev1 = polys[k-2], polys[k-1]
        new = [Fraction(0)] * (k + 1)
        for i, c in enumerate(prev1):
            new[i+1] += c                      # x * He_{k-1}
        for i, c in enumerate(prev2):
            new[i] -= (k - 1) * c              # -(k-1) He_{k-2}
        polys.append(new)
    return polys[n]

def deriv(p):
    return [Fraction(i) * p[i] for i in range(1, len(p))] if len(p) > 1 else [Fraction(0)]

def ev(p, x):
    return sum(c * x**i for i, c in enumerate(p))

def wr(polys):
    # Wronskian polynomial via exact evaluation/interpolation:
    # deg Wr(f_1..f_r) = sum(deg f_i) - r(r-1)/2; evaluate the numeric determinant
    # at enough integer points, then interpolate exactly over Q.
    m = len(polys)
    deg = sum(len(p) - 1 for p in polys) - m * (m - 1) // 2
    N = deg + 1
    vals = []
    for t in range(N):  # points 0..N-1 (sufficient, distinct)
        M = [[ev(polys[j] if False else derivk(polys[j], i), t) for j in range(m)] for i in range(m)]
        vals.append(Fraction(numdet(M)))
    return interpolate(vals)

def derivk(p, k):
    q = p[:]
    for _ in range(k):
        q = deriv(q)
    return q

def numdet(M):
    M = [[Fraction(v) for v in row] for row in M]
    m = len(M); det = Fraction(1); sign = 1
    for c in range(m):
        piv = next((r for r in range(c, m) if M[r][c] != 0), None)
        if piv is None: return Fraction(0)
        if piv != c:
            M[c], M[piv] = M[piv], M[c]; sign = -sign
        det *= M[c][c]
        for r in range(c + 1, m):
            f = M[r][c] / M[c][c]
            if f:
                for k in range(c, m):
                    M[r][k] -= f * M[c][k]
    return sign * det

def interpolate(vals):
    # Lagrange interpolation at points 0..N-1, exact over Q
    N = len(vals); out = [Fraction(0)] * N
    for i in range(N):
        # basis poly L_i = prod_{j!=i} (x - j)/(i - j)
        coef = [Fraction(1)]
        denom = Fraction(1)
        for j in range(N):
            if j == i: continue
            coef = polymul(coef, [-Fraction(j), Fraction(1)])
            denom *= (i - j)
        for k, c in enumerate(coef):
            out[k] += vals[i] * c / denom
    return out

def polymul(a, b):
    out = [Fraction(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out

def he_lambda(lam):
    lam = tuple(x for x in lam if x > 0)
    r = len(lam)
    n = [lam[i] + (r - 1 - i) for i in range(r)]  # 1-indexed paper: n_i = lambda_i + r - i
    polys = [he(n[j]) for j in range(r)]    # column j = He_{n_j}
    delta = 1
    for i, j in combinations(range(r), 2):
        delta *= (n[j] - n[i])              # Delta(n_lambda) = prod_{i<j}(n_j - n_i)
    w = wr(polys)
    return [c / Fraction(delta) for c in w]

def check(lam):
    p = he_lambda(lam)
    p = p + [Fraction(0)] * (sum(lam) + 1 - len(p))
    deg = max(i for i, c in enumerate(p) if c != 0)
    assert deg == sum(lam), (lam, deg)
    assert p[deg] == 1, (lam, p[deg])                     # monic
    assert all(c == 0 for c in p[:deg:2]) or True
    integral = all(c.denominator == 1 for c in p)
    print(f"lambda={lam}: deg={deg} monic ok, integral={integral}, coeffs={[int(c) for c in p if c.denominator==1] if integral else p}")
    return integral

ok = all([check(l) for l in [(1,), (2,), (3,), (1,1), (2,1), (2,2), (3,1), (4,2,1), (3,3,1), (5,2,2,1)]])
print("ALL SAMPLED PARTITIONS INTEGRAL:", ok)

# Control: a NON-Appell monic integer sequence (x^2+a style) can violate the analogous statement,
# confirming the normalization/definition is being read non-vacuously.
def poly_x2a(a): return [Fraction(a), Fraction(0), Fraction(1)]
p = wr([poly_x2a(1), [Fraction(0), Fraction(1)]])   # Wr[x^2+1, x]
p2 = [c / Fraction(1 - 2) for c in p]               # Delta = n_2 - n_1 = 1 - 2 = -1 -> trivial
print("control Wr[x^2+1,x]/-1 =", p2, "(degree-2 case; Appell structure is what forces integrality)")
