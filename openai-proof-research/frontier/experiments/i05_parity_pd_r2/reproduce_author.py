"""Finite falsification checks for i05; these do not prove asymptotic estimates."""
from fractions import Fraction as F
from itertools import product
from math import gcd, log, prod
from pathlib import Path
import json
import random

OUT = Path(__file__).resolve().parent

def lam(n):
    sign, q = 1, 2
    while q*q <= n:
        while n % q == 0:
            n //= q
            sign = -sign
        q += 1
    return -sign if n > 1 else sign

def mu(n):
    sign, q = 1, 2
    while q*q <= n:
        if n % q == 0:
            n //= q
            sign = -sign
            if n % q == 0:
                return 0
        q += 1
    return -sign if n > 1 else sign

rng = random.Random(20261008)
result = {}
cases = 0
for groups in range(1, 6):
    for J in range(1, 5):
        for _ in range(100):
            c = [rng.randrange(J+1) for g in range(groups)]
            free = [rng.choice([3, 5, 7, 11]) for i in range(sum(c))]
            shared = [rng.choice([3, 5, 7, 11]) for i in range(J*groups-sum(c))]
            dr, dc = prod(shared), prod(free)
            w = rng.randrange(1, 100)
            # Evaluate factor-count signs without trial-dividing enormous integers.
            original = (-1)**len(shared)*lam(w)
            predicted = (-1)**(J*groups)*(-1)**len(free)*lam(w)
            assert original == predicted
            if dr*w < 10**7:
                assert lam(dr*w) == predicted
            cases += 1
result['single_endpoint_pattern_sign_cases'] = cases

# Full physical residue orbit, with the pattern sign already independent of labels.
cases = 0
for m in range(1, 33):
    units = [t for t in range(m) if gcd(t, m) == 1]
    for d in units:
        for r in range(m):
            for w in range(m):
                for shared_count in (1, 2):
                    lhs = F(sum((-1)**shared_count * lam(w+1)
                                for t in units
                                if t*w % m == r and t*(w+d) % m == (r+1) % m), len(units))
                    rhs = F((-1)**shared_count * lam(w+1), len(units)) if w % m == r*d % m else F(0)
                    assert lhs == rhs
                    cases += 1
result['signed_orbit_cases'] = cases

# Weighted physical dyads must be reassembled before shared-label mixing.
cases = 0
biased = 0
for m in range(2, 20):
    # An exact uniform residue model; labels here are units carrying a fixed sign.
    units = [t for t in range(1, m) if gcd(t, m) == 1]
    for r in range(m):
        for d in units[:3]:
            for w in range(1, 12):
                total = F(0)
                parts = []
                labels = [m+t for t in units]
                for lo in [2**i for i in range(11)]:
                    part = sum((F(-lam(w), len(units))
                                for label in labels
                                if lo <= label*w < 2*lo
                                and label*w % m == r
                                and label*(w+d) % m == (r+1) % m), F(0))
                    parts.append(part)
                    total += part
                target = F(-lam(w), len(units)) if w % m == r*d % m else F(0)
                assert total == target
                # A per-dyad orbit replacement would apportion total mass by
                # the unrestricted proportion of labels in that physical dyad.
                for lo,part in zip([2**i for i in range(11)],parts):
                    model = target*F(sum(lo <= label*w < 2*lo for label in labels),len(labels))
                    biased += (part != model)
                cases += 1
result['reassembly'] = dict(cases=cases, individually_biased_dyads=biased)

# The determinant Cauchy square is identical after a full Liouville twist.
cases = 0
for bands in [([3, 5],), ([3, 5], [7, 11]), ([3, 5], [7, 11], [13, 17])]:
    K = len(bands)
    labels = [prod(t) for t in product(*bands)]
    for h in range(1, 90):
        rows = []
        signed = []
        for a in labels:
            c = F((a*7+h*3) % 19-9, 11)
            rows.append(c)
            signed.append(c*lam(a*h))
        q0 = sum((a*b for a in rows for b in rows), F(0))
        q1 = sum((a*b for a in signed for b in signed), F(0))
        assert q0 == q1
        assert sum(signed) == (-1)**K*lam(h)*sum(rows)
        cases += 1
result['determinant_square_cases'] = cases

# Low-frequency model: complete multiplicativity, including overlapping factors.
cases = 0
for ell in (3, 5, 15, 35):
    for dd in (1, 2, 4, 6, 15):
        for k in range(1, 16):
            if gcd(ell*dd, k) != 1:
                continue
            for a in range(k):
                lhs = sum(lam(ell*dd*v) for v in range(1, 150)
                          if ell*dd*v % k == a)
                rhs = lam(ell*dd)*sum(lam(v) for v in range(1, 150)
                                        if v % k == a*pow(ell*dd, -1, k) % k)
                assert lhs == rhs
                g = gcd(a,k)
                for v in range(1, 150):
                    if v % k == a:
                        assert v % g == 0 and gcd(v//g, k//g) == 1
                        assert lam(v) == lam(g)*lam(v//g)
                cases += 1
result['signed_divisor_and_nonunit_cases'] = cases

# Positive parity splitting used in the block sieve; no signed positivity claim.
cases = 0
for n in range(1, 1000):
    wt = F(n % 13, 7)
    wp = wt*(1+lam(n))/2
    wm = wt*(1-lam(n))/2
    assert wp >= 0 and wm >= 0 and wp+wm == wt and wp-wm == wt*lam(n)
    cases += 1
result['positive_sieve_split_cases'] = cases

# Exact factor allocation retains lambda(u) externally, not lambda(v).
cases = 0
for j in range(2, 6):
    for u in range(1, 100):
        for hits in range(1, 10):
            for groups in range(1, min(hits, 4)+1):
                q = F(1, 2)
                lhs = lam(u)*j**hits*(q/j)**(hits-groups)
                rhs = lam(u)*j**groups*q**(hits-groups)
                assert lhs == rhs
                cases += 1
result['signed_allocation_cases'] = cases

result['counterexamples'] = {
    'E_band_vs_full_sign': {'active_primes':[3,5], 'prime_endpoint':7, 'band_sign':1, 'lambda':lam(7)},
    'mobius_shared_overlap': {'D':2,'w':2,'wprime':3,
                              'mu_Dw_mu_Dwprime':mu(4)*mu(6),'mu_w_mu_wprime':mu(2)*mu(3)},
    'discrepancy_not_stable_under_lambda': {'m':[2,4],'alpha':[1,-2],
                                           'untwisted_reciprocal':str(F(1,2)-F(2,4)),
                                           'twisted_reciprocal':str(-F(1,2)-F(2,4))},
    'carella_sign_identity': {'Nplus':7,'Nminus':3,'Q':10,'S':4,
                             'correct_Nplus':str(F(10+4,2)),
                             'correct_Nminus':str(F(10-4,2)),
                             'incorrect_Nminus_plus_sign':str(F(10+4,2))},
}

# Exact prime statistics are a falsification screen, not a convergence assertion.
N = 1_000_000
spf = list(range(N+1))
for p in range(2, int(N**.5)+1):
    if spf[p] == p:
        for n in range(p*p, N+1, p):
            if spf[n] == n:
                spf[n] = p
la = [1]*(N+1)
mob = [1]*(N+1)
for n in range(2, N+1):
    p = spf[n]
    la[n] = -la[n//p]
    mob[n] = 0 if (n//p) % p == 0 else -mob[n//p]
rows = []
for M,b in ((1,0),(4,1),(4,3),(8,5),(9,1),(9,2),(12,7)):
    ps = [p for p in range(3, N+1) if spf[p] == p and p % M == b]
    counts = {(sg,sq):0 for sg in (-1,1) for sq in (0,1)}
    for p in ps:
        counts[la[p-1],int(mob[p-1]!=0)] += 1
    assert sum(counts.values()) == len(ps)
    if (M,b) in ((4,1),(9,1),(8,5)):
        assert counts[-1,1] == counts[1,1] == 0
    rows.append(dict(M=M,b=b,prime_count=len(ps),lambda_sum=sum(la[p-1] for p in ps),
                     mu_sum=sum(mob[p-1] for p in ps),
                     counts={f'lambda={s},squarefree={q}':v for (s,q),v in counts.items()}))
result['finite_prime_screen'] = dict(limit=N, rows=rows)
result['meaning'] = 'All exact identities passed; this is neither an asymptotic proof nor a novelty certificate.'
(OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k != 'finite_prime_screen'},indent=2))
