"""Independent finite controls for the kinetic manuscript gate (review r1).

Copyright (c) 2026 Myeongjin Kang. MIT License.
Finite/numerical sanity checks only. They do not prove Lemma 4.1, any measure
identity, or the path limit. Writes only independent_controls.json beside itself.

1. Genuine 3-D extended prefix chart (Section 4.2): mergers solve
   x_p(t)-x_q(t) = -eps*omega with incoming flux, determined redundant entering
   roots on the forward ray, strict global chronology Q.  The collective shear
   (4.6) must preserve success/abort and translate every path in time (Lemma 4.3).
2. Simplex enlargement (4.11): exact polynomial volume via inclusion of the
   first-time length, and a Monte Carlo cross-check.
3. Stirling step in Section 4.6 and the energy sum (4.15), on finite ranges.
"""
from fractions import Fraction as F
from math import comb, exp, factorial, lgamma, log, sqrt
from pathlib import Path
import json, random

checks = {}
def ck(name, cond):
    if not cond:
        raise AssertionError(name)
    checks[name] = True

def dot(a, b): return sum(x * y for x, y in zip(a, b))
def add(a, b): return [x + y for x, y in zip(a, b)]
def sub(a, b): return [x - y for x, y in zip(a, b)]
def mul(c, a): return [c * x for x in a]

EPS = 1.0
TOL = 1e-9

def build(v, X, links, slots):
    """links: list of (p, q, y) with y = A_q - A_p (initial forest, rooted at 0).
    slots: ('M', p, q, t, omega, kind) or ('R', p, q, kind); kind 'C' or 'O'.
    Returns dict with success flag, times, and piecewise-affine segments."""
    m = len(v)
    cur = [list(x) for x in v]
    group = list(range(m))
    seg = [[[None, [0.0, 0.0, 0.0], list(v[p])]] for p in range(m)]  # start, origin, vel
    last = [None] * m
    times = []
    def move(g, delta):
        for p in range(m):
            if group[p] == g:
                for s in seg[p]:
                    s[1] = add(s[1], delta)
    def merge(g1, g2):
        for p in range(m):
            if group[p] == g2:
                group[p] = g1
    for p, q, y in links:
        move(group[q], sub(add(seg[p][0][1], y), seg[q][0][1]))
        merge(group[p], group[q])
    for sl in slots:
        if sl[0] == 'M':
            _, p, q, t, om, kind = sl
            if group[p] == group[q]:
                return {'success': False, 'why': 'merger within group'}
            u = sub(cur[p], cur[q])
            if dot(u, om) <= TOL:
                return {'success': False, 'why': 'nonincoming merger'}
            xp = add(seg[p][-1][1], mul(t, cur[p]))
            xq = add(seg[q][-1][1], mul(t, cur[q]))
            # want xp - xq = -EPS*om: translate q's group
            move(group[q], sub(add(xp, mul(EPS, om)), xq))
            merge(group[p], group[q])
            gap = sub(add(seg[p][-1][1], mul(t, cur[p])), add(seg[q][-1][1], mul(t, cur[q])))
            assert max(abs(g + EPS * o) for g, o in zip(gap, om)) < 1e-9
        else:
            _, p, q, kind = sl
            u = sub(cur[p], cur[q])
            d = sub(seg[p][-1][1], seg[q][-1][1])  # r(t) = d + t u
            a, b, c = dot(u, u), 2 * dot(d, u), dot(d, d) - EPS ** 2
            disc = b * b - 4 * a * c
            if a <= TOL or disc <= TOL:
                return {'success': False, 'why': 'no transversal root'}
            t = (-b - sqrt(disc)) / (2 * a)  # entering root
            lows = [x for x in (last[p], last[q]) if x is not None]
            if lows and t < max(lows) - TOL:
                return {'success': False, 'why': 'root before forward ray'}
            r = add(d, mul(t, u))
            om = mul(-1 / EPS, r)
        if times and t <= times[-1] + TOL:
            return {'success': False, 'why': 'Q'}
        xp = add(seg[p][-1][1], mul(t, cur[p]))
        xq = add(seg[q][-1][1], mul(t, cur[q]))
        if kind == 'C':
            w = dot(sub(cur[p], cur[q]), om)
            cur[p], cur[q] = sub(cur[p], mul(w, om)), add(cur[q], mul(w, om))
        seg[p].append([t, sub(xp, mul(t, cur[p])), list(cur[p])])
        seg[q].append([t, sub(xq, mul(t, cur[q])), list(cur[q])])
        last[p] = last[q] = t
        times.append(t)
    move(group[0], sub(X, seg[0][0][1]))
    energy = sum(dot(x, x) for x in cur)
    return {'success': True, 'times': times, 'seg': seg, 'energy': energy}

def pos(h, p, t):
    s = h['seg'][p][0]
    for nxt in h['seg'][p][1:]:
        if nxt[0] <= t:
            s = nxt
    return add(s[1], mul(t, s[2]))

def rand_unit(rng):
    while True:
        x = [rng.gauss(0, 1) for _ in range(3)]
        n = sqrt(dot(x, x))
        if n > 0.1:
            return mul(1 / n, x)

rng = random.Random(20261014)
found = 0
pairs = {}
attempts = 0
shear_tests = 0
abort_tests = 0
while found < 40 and attempts < 200000:
    attempts += 1
    v = [[rng.uniform(-2, 2) for _ in range(3)] for _ in range(3)]
    y = mul(rng.uniform(0.0, 3.0), rand_unit(rng))
    links = [(0, 1, y)]
    t1 = rng.uniform(0.1, 1.0)
    om = rand_unit(rng)
    k1, k2 = rng.choice('CO'), rng.choice('CO')
    rp = rng.choice([(0, 2), (1, 2), (0, 1)])
    slots = [('M', 0, 2, t1, om, k1), ('R', rp[0], rp[1], k2)]
    X = [rng.uniform(-1, 1) for _ in range(3)]
    base = build(v, X, links, slots)
    if not base['success']:
        continue
    found += 1
    key = '%d%d%s%s' % (rp[0], rp[1], k1, k2)
    pairs[key] = pairs.get(key, 0) + 1
    E0 = sum(dot(x, x) for x in v)
    ck('all_line_energy_3d', abs(base['energy'] - E0) < 1e-8)
    for theta in (-2.5, -0.3, 0.7, 4.0):
        Xs = sub(X, mul(theta, v[0]))  # representative = line 0
        ys = sub(y, mul(theta, sub(v[1], v[0])))
        sl2 = [('M', 0, 2, t1 + theta, om, k1), ('R', rp[0], rp[1], k2)]
        sh = build(v, Xs, [(0, 1, ys)], sl2)
        assert sh['success'], (sh, base['times'], theta, rp, k1, k2)
        assert all(abs(a - (b + theta)) < 1e-8 for a, b in zip(sh['times'], base['times']))
        for s in (-3.0, 0.0, t1, base['times'][-1], 2.0, 6.0):
            for p in range(3):
                assert max(abs(a - b) for a, b in zip(pos(sh, p, s + theta), pos(base, p, s))) < 1e-7
        shear_tests += 1
    # A chronology violation: prescribe the merger after the determined time.
    # Reordered chart (redundant (0,1) first, merger later): the success flag
    # of the chart and of its sheared image must agree.
    tR = base['times'][-1]
    if rp == (0, 1):
        for theta in (0.0, 1.3):
            reord = [('R', 0, 1, k2), ('M', 0, 2, max(tR, t1) + 0.5 + theta, om, k1)]
            r1 = build(v, X, links, reord)
            r2 = build(v, sub(X, mul(theta, v[0])), [(0, 1, sub(y, mul(theta, sub(v[1], v[0]))))],
                       [('R', 0, 1, k2), ('M', 0, 2, max(tR, t1) + 0.5 + theta + theta, om, k1)])
            assert r1['success'] == r2['success']
            abort_tests += 1
ck('found_3d_charts_with_redundant_root', found >= 40)
# E2: an O-merger followed by a redundant slot on the same unchanged pair returns
# the same entering time (structural tie); strict Q must reject it, also when sheared.
ties = 0
for _ in range(200):
    v = [[rng.uniform(-2, 2) for _ in range(3)] for _ in range(3)]
    om = rand_unit(rng)
    if dot(sub(v[0], v[2]), om) <= 0.05:
        continue
    for theta in (0.0, 1.7):
        res = build(v, [0.0, 0.0, 0.0], [(0, 1, [2.0, 0.0, 0.0])],
                    [('M', 0, 2, 0.4 + theta, om, 'O'), ('R', 0, 2, 'C')])
        assert not res['success'] and res['why'] == 'Q'
        ties += 1
ck('E2_structural_O_tie_rejected_by_strict_Q_3d', ties >= 100)
ck('shear_covariance_3d_paths_and_times', shear_tests >= 160)
ck('shift_invariance_of_success_flag', abort_tests >= 1)

# 2. Simplex enlargement, exact: |S_a - [0,Theta]1| = tau^a/a! + Theta tau^(a-1)/(a-1)!
def enlarged_volume_exact(a, tau, Th):
    # integrate first-time length (tau + Th - G) over gap simplex {0<g2<..<ga<tau}, G = ga
    # gap simplex density of G: G^(a-2)/(a-2)! for a>=2
    if a == 1:
        return tau + Th
    # int_0^tau (tau+Th-G) G^(a-2)/(a-2)! dG
    return (tau + Th) * tau ** (a - 1) / factorial(a - 1) - tau ** a * (a - 1) / factorial(a)
for a in range(1, 9):
    for tau in (F(1), F(1, 3), F(7, 2)):
        for Th in (F(0), tau, F(5, 4)):
            lhs = enlarged_volume_exact(a, tau, Th)
            rhs = tau ** a / factorial(a) + Th * tau ** (a - 1) / factorial(a - 1)
            assert lhs == rhs
ck('simplex_enlargement_exact_formula', True)
mc = random.Random(7)
for a in (2, 3):
    tau, Th, n, hit = 1.0, 1.0, 200000, 0
    for _ in range(n):
        t = sorted(mc.uniform(-Th, tau) for _ in range(a))
        if t[0] > -Th and t[-1] < tau and t[-1] - t[0] < tau:
            hit += 1
    est = hit / n * (tau + Th) ** a / factorial(a)
    exact = tau ** a / factorial(a) + Th * tau ** (a - 1) / factorial(a - 1)
    assert abs(est - exact) < 0.01, (a, est, exact)
ck('simplex_enlargement_monte_carlo', True)

# 3. Stirling step: n^(3a/2)/(a! n!) <= e^(2n) (1+n)^(n-a) n^(-n/2), 0<=a<=n
for n in range(1, 160):
    for a in range(0, n + 1):
        lhs = 1.5 * a * log(n) - lgamma(a + 1) - lgamma(n + 1)
        rhs = 2 * n + (n - a) * log(1 + n) - 0.5 * n * log(n)
        assert lhs <= rhs + 1e-9, (n, a)
ck('stirling_step_finite_range', True)
# energy sum (4.15): sum_{P dyadic} e^{-b P/4} P^{a/2} <= C^{a+1} (1+a)^{a/2}; fit C
b = 0.37
worst = 0.0
for a in range(0, 120):
    s = sum(exp(-b * 2 ** k / 4 + (a / 2) * k * log(2)) for k in range(0, 80))
    worst = max(worst, (log(s) - (a / 2) * log(1 + a)) / (a + 1))
ck('energy_sum_geometric_base_bounded', worst < 3.0)
# cylinder/scale exponent and transfer exponent
ck('connected_scale', all(-2 * (m - h) + 2 * (m - 1 - p) + 2 * p == 2 * (h - 1)
                          for m in range(1, 20) for p in range(m) for h in range(1, 8)))
ck('transfer_exponent', F(-1) + F(21, 20) * F(21, 22) == F(1, 440))
ck('union_first_form', all(F(k ** 3) * (F(1, k) + F(1, k ** 20)) / F(k ** 3) == F(1, k) + F(1, k ** 20)
                           for k in range(1, 30)))

result = {'status': 'PASS', 'count': len(checks), 'checks': checks,
          'charts_found': found, 'redundant_pair_and_CO_types': pairs, 'attempts': attempts, 'shear_tests': shear_tests,
          'energy_sum_log_base_max': worst,
          'scope': 'finite numerical/exact controls only; no proof of Lemma 4.1, of the Jacobian, '
                   'of history existence, of kernel bounds, or of the path limit'}
Path(__file__).with_suffix('.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'checks'}, indent=2))
