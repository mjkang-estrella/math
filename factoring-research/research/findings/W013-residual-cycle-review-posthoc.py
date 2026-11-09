"""POST-HOC (not preregistered) structural check on the same fixed N and cycle as C3.
Prediction from the ideal dictionary: a 'mixed' collision requires |a| to have at
least two distinct prime factors not dividing 4N; prime-power |a| only allows the
'conjugate' type. Fixed input; no sweep."""
import itertools, json
from math import gcd, isqrt
N = 22117019; q0 = isqrt(N)
def pf(m):
    s, d = set(), 2
    while d * d <= m:
        while m % d == 0: s.add(d); m //= d
        d += 1
    if m > 1: s.add(m)
    return s
cyc, P, Qp, Q, n, start = [], q0, 1, N - q0 * q0, 1, None
while True:
    f = ((-1) ** (n - 1) * Qp, P)
    if start is None: start = f
    elif f == start: break
    cyc.append(f); q = (q0 + P) // Q; Pn = q * Q - P; P, Qp, Q = Pn, Q, (N - Pn * Pn) // Q; n += 1
by = {}
for (a, P) in cyc: by.setdefault(a, []).append(P)
res = {"mixed_min_unramified_primes": None, "mixed_violations": 0, "conj_with_prime_power_abs_a": 0,
       "mixed_total": 0, "conj_total": 0}
mins = []
for a, Ps in by.items():
    un = {p for p in pf(abs(a)) if (4 * N) % p}
    for Pi, Pj in itertools.combinations(Ps, 2):
        m = abs(a)
        if (Pi + Pj) % m == 0:
            res["conj_total"] += 1; res["conj_with_prime_power_abs_a"] += len(pf(m)) == 1
        elif (Pi - Pj) % m:
            res["mixed_total"] += 1; mins.append(len(un)); res["mixed_violations"] += len(un) < 2
res["mixed_min_unramified_primes"] = min(mins)
res["ok"] = res["mixed_violations"] == 0
print(json.dumps(res, sort_keys=True))
