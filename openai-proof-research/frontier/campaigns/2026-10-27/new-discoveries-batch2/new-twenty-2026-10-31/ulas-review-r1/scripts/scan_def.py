"""Independent reviewer scan (ulas-review-r1). Exact Python integers.
c_m(n) from the DEFINITION C(x)^m, C(x) = 1/(1-x) * prod_{i>=0} 1/(1-x^{2^i}):
C^m = C^{m-1} * C is obtained by multiplying the series by the geometric series
1/(1-x^s) (s = 1, 1, 2, 4, 8, ...), i.e. f[n] += f[n-s] in increasing n.
Checks Conjecture 6.1 and the r130 claims for m in [m_lo, m_hi], n in [1, nmax]."""
import sys, json, hashlib
m_lo, m_hi, nmax = map(int, sys.argv[1:4])
L = 4 * nmax + 1

def v2(x):
    if x == 0: return None  # infinite valuation
    x = abs(x); return (x & -x).bit_length() - 1

def mul_C(f):
    f = f[:]
    steps = [1, 1]; s = 2
    while s < L: steps.append(s); s *= 2
    for s in steps:
        for n in range(s, L): f[n] += f[n - s]
    return f

f = [1] + [0] * (L - 1)   # C^0
out = []
H = hashlib.sha256()
for m in range(1, m_hi + 1):
    f = mul_C(f)
    if m < m_lo: continue
    exc = {}; viol = []; eqset = []; zero = []
    for n in range(1, nmax + 1):
        d = f[4 * n] - f[n]; v = v2(d); vn = v2(n)
        H.update(f"{m},{n},{v};".encode())
        if v is None: zero.append(n); continue
        if m % 2 == 0:
            k = m // 2; target = vn + 2 * v2(k) + 3; e = v - target
            if e != 0: viol.append((n, v, target))
        elif m % 4 == 1:
            e = v - (vn + 3)
            if e < 0: viol.append((n, v, vn + 3))
        else:
            e = v - (vn + 6)
            if e < 0: viol.append((n, v, vn + 6))
        exc[e] = exc.get(e, 0) + 1
        if e == 0: eqset.append(n)
    # compare equality set with the r130 claimed equality sets (Theorem parts 2,3)
    r = m % 16
    if m % 2 == 0: claim = "all n"; pred = lambda n: True
    elif m % 4 == 1: claim = "odd n (claimed: every odd n is equality)"; pred = lambda n: n % 2 == 1
    elif r in (3, 7): claim = "odd n"; pred = lambda n: n % 2 == 1
    elif r == 11: claim = "n = 2 mod 4"; pred = lambda n: n % 4 == 2
    else: claim = "never"; pred = lambda n: False
    claimed_eq = [n for n in range(1, nmax + 1) if pred(n)]
    missing = sorted(set(claimed_eq) - set(eqset))   # claimed equality but not observed
    extra = sorted(set(eqset) - set(claimed_eq))      # observed equality outside claimed set
    # minimum excess when m = 3 mod 4 compared with max(6, v2(m+1)+3) (observed, unclaimed)
    rec = dict(m=m, violations=viol[:10], n_violations=len(viol), zero_diffs=zero[:10],
               excess_hist=dict(sorted(exc.items())), min_excess=min(exc) if exc else None,
               claimed_equality_set=claim, claimed_but_not_equal=missing[:10], n_claimed_but_not_equal=len(missing),
               equal_outside_claim=extra[:10], n_equal_outside_claim=len(extra),
               equality_count=len(eqset), first_equalities=eqset[:6])
    if m % 4 == 3: rec["sharp_const_guess_max6_v2m1p3"] = max(6, v2(m + 1) + 3)
    out.append(rec)
    print(json.dumps(rec), flush=True)
print("final m", m_hi, "c_m(1..4) =", f[1:5])
print("valuation-table sha256", H.hexdigest())
