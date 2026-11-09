#!/usr/bin/env python3
"""Exact verification that n=170 refutes Dolfi-Hafezieh-Spiga Conjecture 1 (arXiv:2402.19335v1).
Pure Python, deterministic. Checks:
 (1) 170 = 2*5*17 has exactly 3 distinct prime factors;
 (2) gcd(2^170-1, 170) = 1;
 (3) 2^170-1 = 3*11*31*43691*131071*9520972806333758431*26831423036065352611 exactly;
 (4) each factor is prime: small ones by trial division, the two 19/20-digit ones by
     deterministic Miller-Rabin with the first 13 prime bases (valid for n < 3.317e24,
     Sorenson-Webster 2015) AND by an independent Pocklington-Lehmer certificate;
 (5) hence 2^170-1 has exactly 7 < 8 = 2^3 distinct prime divisors.
"""
import math, json, sys
n = 170
N = 2**n - 1
F = [3, 11, 31, 43691, 131071, 9520972806333758431, 26831423036065352611]
def trial_prime(m):
    if m < 2: return False
    i = 2
    while i * i <= m:
        if m % i == 0: return False
        i += 1
    return True
def mr_det(m):
    bases = [2,3,5,7,11,13,17,19,23,29,31,37,41]
    assert m < 3317044064679887385961981
    if m < 2: return False
    for p in bases:
        if m % p == 0: return m == p
    d, s = m - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in bases:
        x = pow(a, d, m)
        if x in (1, m - 1): continue
        for _ in range(s - 1):
            x = x * x % m
            if x == m - 1: break
        else: return False
    return True
def factor_small(m, bound=10**7):
    f = {}; p = 2
    while p * p <= m and p <= bound:
        while m % p == 0: f[p] = f.get(p, 0) + 1; m //= p
        p += 1 if p == 2 else 2
    return f, m
def pocklington(m):
    """Pocklington-Lehmer: if F | m-1 fully factored with F > sqrt(m) and for each prime q|F there is a
    with a^(m-1) = 1 and gcd(a^((m-1)/q)-1, m)=1, then m is prime. Returns certificate or None."""
    f, cof = factor_small(m - 1)
    Fpart = 1
    for q, e in f.items(): Fpart *= q**e
    if cof > 1 and cof < 10**15 and trial_prime(cof):
        f[cof] = 1; Fpart *= cof; cof = 1
    if Fpart * Fpart <= m: return None
    cert = {}
    for q in f:
        for a in range(2, 200):
            if pow(a, m - 1, m) != 1: return None
            if math.gcd(pow(a, (m - 1) // q, m) - 1, m) == 1:
                cert[str(q)] = a; break
        else: return None
    return {"m_minus_1_factored_part": {str(k): v for k, v in f.items()}, "unfactored_cofactor": cof, "witnesses": cert}
out = {}
_f,_c = factor_small(n)
out["distinct_prime_factors_of_n"] = sorted(list(_f.keys()) + ([_c] if _c > 1 else []))
assert out["distinct_prime_factors_of_n"] == [2, 5, 17]
out["gcd"] = math.gcd(N, n); assert out["gcd"] == 1
prod = 1
for p in F: prod *= p
assert prod == N, "factorization mismatch"
out["product_matches"] = True
assert len(set(F)) == 7
prim = {}
for p in F:
    if p < 10**12:
        ok = trial_prime(p); prim[str(p)] = {"trial_division": ok}
    else:
        prim[str(p)] = {"deterministic_MR_13_bases": mr_det(p), "pocklington": pocklington(p)}
        ok = prim[str(p)]["deterministic_MR_13_bases"] and prim[str(p)]["pocklington"] is not None
    assert ok, p
out["primality"] = prim
# multiplicative orders: each prime factor's order of 2 mod p, showing they are primitive divisors of distinct d | 170
def order2(p):
    for d in sorted(dd for dd in range(1, n + 1) if n % dd == 0):
        if pow(2, d, p) == 1: return d
out["order_of_2_mod_each_factor"] = {str(p): order2(p) for p in F}
out["distinct_prime_divisors_of_2^170-1"] = len(F)
out["bound_2^ell"] = 8
out["conclusion"] = "2^170-1 has exactly 7 < 8 distinct prime divisors; Conjecture 1 fails at n=170"
json.dump(out, sys.stdout, indent=1); print()
