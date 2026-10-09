"""Finite falsification checks only; no asymptotic or novelty certification."""
from itertools import combinations, product
from math import gcd, prod
from pathlib import Path
import json


def factors(n):
    n = abs(n)
    d, out = 2, {}
    while d * d <= n:
        while n % d == 0:
            out[d] = out.get(d, 0) + 1
            n //= d
        d += 1
    if n > 1:
        out[n] = out.get(n, 0) + 1
    return out


def primes(n):
    s = bytearray(b'\1') * (n + 1)
    s[:2] = b'\0\0'
    for p in range(2, int(n**0.5) + 1):
        if s[p]:
            s[p*p:n+1:p] = b'\0' * ((n-p*p)//p+1)
    return [p for p in range(2, n + 1) if s[p]]


def square_vector(a, ps):
    f = factors(a)
    return (int(a < 0),) + tuple(f.get(p, 0) % 2 for p in ps)


def cubic_vector(a, ps):
    f = factors(a)
    return tuple(f.get(p, 0) % 3 for p in ps)


def dot(a, b, q):
    return sum(x*y for x, y in zip(a, b)) % q


def quadratic_at_residue(a, u):
    """Reciprocity formula, with u a positive odd unit at primes dividing a."""
    r = (-1 if u % 4 == 3 else 1) if a < 0 else 1
    for p, e in factors(a).items():
        if not e % 2:
            continue
        if p == 2:
            r *= 1 if u % 8 in (1, 7) else -1
        else:
            r *= 1 if pow(u % p, (p-1)//2, p) == 1 else -1
            if p % 4 == 3 and u % 4 == 3:
                r *= -1
    return r


def order(a, p, fp):
    n = p - 1
    for q in fp:
        while n % q == 0 and pow(a, n//q, p) == 1:
            n //= q
    return n


def criteria(A):
    ps = sorted(set([3] + [p for a in A for p in factors(a)]))
    vs = [square_vector(a, ps) for a in A]
    chars = [t for t in product(range(2), repeat=len(ps)+1)
             if all(dot(v, t, 2) == 1 for v in vs)]
    vminus3 = square_vector(-3, ps)
    avoid3 = any(dot(vminus3, t, 2) == 1 for t in chars)
    cv = [cubic_vector(a, ps) for a in A]
    cube_chars = [t for t in product(range(3), repeat=len(ps))
                  if all(dot(v, t, 3) != 0 for v in cv)]
    return dict(quadratic_compatible=bool(chars), avoids_three=avoid3,
                forced_three=bool(chars) and not avoid3,
                cubic_compatible=bool(cube_chars),
                classical_positive=bool(chars) and (avoid3 or bool(cube_chars)))


pool = [-18, -12, -9, -6, -4, -3, -2, 2, 3, 4, 5, 6, 8, 12, 18, 27]
ps = [2, 3, 5]
M = 8 * 3 * 5
units = [u for u in range(1, M) if gcd(u, M) == 1]
signs = {u: {a: quadratic_at_residue(a, u) for a in pool} for u in units}
quad_checks = certificate_checks = partial_checks = 0
for k in range(1, 5):
    for A in combinations(pool, k):
        c = criteria(A)
        actual = [u for u in units if all(signs[u][a] == -1 for a in A)]
        assert bool(actual) == c['quadratic_compatible']
        quad_checks += 1
        cert = [u for u in actual if u % 3 != 1 and u % 5 != 1]
        assert bool(cert) == c['avoids_three']
        certificate_checks += 1
        partial = [u for u in actual if u % 5 != 1]
        assert bool(partial) == c['quadratic_compatible']
        # Any such residue can be lifted to cap v_3(p-1) at one.
        for u in partial:
            assert any((u+j*M-1) % 9 != 0 for j in range(3))
        partial_checks += 1

examples = [[2, 3, 6], [2, -6], [8, -24], [5, -15, 600, 1029],
            [-4, 2], [4], [-8], [2, 3, 5, 7], [-2, -3, 6]]
example_results = [{'bases': A, **criteria(A)} for A in examples]

# Exact finite Kummer group calculation for {2,-6}.
translations = list(product(range(3), repeat=2))
cube_good = [list(v) for v in translations if v[0] and (v[0]+v[1]) % 3]
assert len(cube_good) == 4
# Four projective directions cover F_3^2 by their zero hyperplanes.
cover = [(1, 0), (0, 1), (1, 1), (2, 1)]
assert all(any(dot(v, t, 3) == 0 for v in cover) for t in translations)

P = primes(300000)
counts = {str(b): {'primes': 0, 'cubic_good': 0, 'joint_primitive': 0,
                  'first_cubic_good': None, 'first_cubic_bad': None}
          for b in (13, 19)}
reciprocity_checks = 0
universal_checks = index_three_checks = nonvacuous_good = 0
all_A = [-27, -18, -12, -9, -8, -6, -4, -3, -2,
         2, 3, 4, 5, 6, 8, 9, 12, 16, 18, 27, 64]
fp_cache = {p: factors(p-1) for p in P if p > 3}
for p in P:
    if p <= 7:
        continue
    for a in pool:
        if p % abs(a) != 0 and a % p:
            assert quadratic_at_residue(a, p) == (1 if pow(a, (p-1)//2, p) == 1 else -1)
            reciprocity_checks += 1
    fp = fp_cache[p]
    if p % 24 in (13, 19):
        d = counts[str(p % 24)]
        d['primes'] += 1
        good = all(pow(a, (p-1)//3, p) != 1 for a in (2, -6))
        d['cubic_good'] += good
        d['joint_primitive'] += all(order(a, p, fp) == p-1 for a in (2, -6))
        key = 'first_cubic_good' if good else 'first_cubic_bad'
        if d[key] is None:
            d[key] = p
    # Direct finite logic, not the tiny-exponent asymptotic: remove every
    # forbidden index prime explicitly and test the claimed surviving index.
    for a in all_A:
        if a % p == 0:
            continue
        idx = (p-1)//order(a, p, fp)
        no_odd_obstruction = all(pow(a, (p-1)//q, p) != 1 for q in fp if q != 2)
        if p % 4 == 3 and no_odd_obstruction:
            assert idx in (1, 2)
            universal_checks += 1
        no_large_obstruction = all(pow(a, (p-1)//q, p) != 1 for q in fp if q >= 5)
        if (p-1) % 9 != 0 and pow(a, (p-1)//2, p) == p-1 and no_large_obstruction:
            assert idx in (1, 3)
            index_three_checks += 1
    # Nonvacuous simultaneous bound 2 for a fixed mixed signed/power set.
    if p % 4 == 3 and all((p-1)//order(a, p, fp) <= 2 for a in all_A):
        nonvacuous_good += 1

result = dict(
    scope='Finite algebra only; does not test PD, zero-free strips, or positive density.',
    quadratic_system_checks=quad_checks,
    avoid_three_certificate_checks=certificate_checks,
    index_three_class_checks=partial_checks,
    reciprocity_checks=reciprocity_checks,
    example_criteria=example_results,
    cubic_good_translations=cube_good,
    cubic_hyperplane_cover_checked=len(translations),
    prime_bound=300000,
    pair_2_minus6_by_residue=counts,
    finite_index_two_survivors=universal_checks,
    finite_index_three_survivors=index_three_checks,
    simultaneous_index_at_most_two_count=nonvacuous_good,
    simultaneous_bases=all_A,
    failures=0,
)
path = Path(__file__).with_name('results.json')
path.write_text(json.dumps(result, indent=2)+'\n')
print(json.dumps(result, indent=2))
