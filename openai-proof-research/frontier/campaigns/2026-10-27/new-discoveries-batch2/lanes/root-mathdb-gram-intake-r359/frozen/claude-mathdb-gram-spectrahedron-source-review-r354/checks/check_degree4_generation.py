"""Threshold m*(n) and exact (mod-p certified) degree-4 generation ranks.

m*(n) := max{m : m N - C(m,2) < C(n+3,4)},  N = C(n+1,2).
For fixed integer quadrics, rank over F_p <= rank over Q, and dim (q)_4 <= mN - C(m,2) (Koszul).
So rank_p == C(n+3,4) certifies (q)_4 = S_4 over Q; rank_p == mN - C(m,2) certifies equality.
These are INSTANCE helpers (n <= 8), not a general theorem. Exit 0 iff all asserted certificates hold.
"""
import json
import random
import sys
from math import comb

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from gramlib import quad_monomials, quartic_monomials, add, rank_mod_p

P = 2**31 - 1
R349 = {2: 1, 3: 2, 4: 4, 5: 5, 6: 6, 7: 8, 8: 10, 9: 12, 10: 14}


def mstar(n):
    N = comb(n + 1, 2)
    return max(m for m in range(0, N + 1) if m * N - comb(m, 2) < comb(n + 3, 4))


def ideal4_rank(n, m, seed):
    rng = random.Random(seed)
    v = quad_monomials(n)
    quart = quartic_monomials(n)
    qi = {e: i for i, e in enumerate(quart)}
    qs = [[rng.randint(-50, 50) for _ in v] for _ in range(m)]
    rows = []
    for q in qs:
        for g in v:
            row = [0] * len(quart)
            for c, e in zip(q, v):
                row[qi[add(e, g)]] += c
            rows.append(row)
    return rank_mod_p(rows, P), qs


res = {}
ok = True
for n in range(2, 9):
    N = comb(n + 1, 2)
    ms = mstar(n)
    S4 = comb(n + 3, 4)
    r_up, _ = ideal4_rank(n, ms + 1, seed=1000 + n)
    r_at, _ = ideal4_rank(n, ms, seed=2000 + n)
    koszul = ms * N - comb(ms, 2)
    entry = {'N': N, 'dimS4': S4, 'mstar': ms, 'r349_T2_value': R349.get(n),
             'rank_(mstar+1)_tuple': r_up, 'certifies_S4_generated_at_mstar+1': r_up == S4,
             'rank_mstar_tuple': r_at, 'koszul_bound_at_mstar': koszul,
             'certifies_expected_dim_at_mstar': r_at == koszul,
             'dim_I4_perp_at_mstar': S4 - koszul}
    ok &= (r_up == S4) and (r_at == koszul) and (R349.get(n) in (None, ms))
    res[n] = entry
for n in range(9, 11):
    res[n] = {'mstar': mstar(n), 'r349_T2_value': R349[n]}
    ok &= mstar(n) == R349[n]
res['status'] = 'PASS' if ok else 'FAIL'
print(json.dumps(res, indent=1))
sys.exit(0 if ok else 1)
