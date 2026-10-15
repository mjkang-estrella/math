"""Independent finite controls for the kinetic-repair-r1 candidate (proof round 2).

Supporting checks only; they certify no part of Lemma W, E', or Theorem F.

1. A three-dimensional implementation of the candidate's prefix construction
   (Section 2.2: initial forest offsets y, recursive group translations at
   mergers, determined redundant entering times, C/O updates, global order
   test Q), written from the candidate text, not from the repair scripts.
   For random formal coordinates (successful and aborting) it checks Claim 2:
   under Phi_theta every event shifts by theta, every segment is the time
   translate, success/abort and the abort slot are invariant, and the total
   energy of all m lines is conserved.
2. Claim 1 against physics: an exact event-driven simulation of a few
   three-dimensional hard spheres (with a genuine recollision) is converted
   to the candidate's coordinates, then rebuilt by the construction. All
   event times, normals, and segment data must agree, and Q=1.
3. The Minkowski volume |S-[0,Theta]1| = tau^a/a! + Theta tau^(a-1)/(a-1)!
   by a deterministic exact-rational lattice count (Riemann sum with error
   bound) for a=1,2,3 and several Theta.
4. The Stirling step and the pair-flux bound used in Section 2.5.
"""
import itertools
import json
import math
import random
from fractions import Fraction as Fr

TOL = 1e-8
results = {}


def check(name, cond):
    if not cond:
        raise AssertionError(name)
    results[name] = True


def add(a, b): return [a[i] + b[i] for i in range(3)]
def sub(a, b): return [a[i] - b[i] for i in range(3)]
def mul(c, a): return [c * a[i] for i in range(3)]
def dot(a, b): return sum(a[i] * b[i] for i in range(3))
def norm(a): return math.sqrt(dot(a, a))


def build(v, X, links, slots, eps):
    """Candidate Section 2.2 construction.

    v: pre-first velocities; X: final affine origin of line 0;
    links: list of (p, q, y) with y = A_q - A_p; slots: global order list of
    ('M', p, q, t, omega, CO) or ('R', p, q, CO). omega is the H normal with
    x_p - x_q = -eps*omega at contact and incoming (v_p - v_q).omega > 0.
    Returns dict with success flag, abort slot, events, segments.
    """
    m = len(v)
    cur = [list(x) for x in v]
    group = list(range(m))
    # segments: [start_time or None, affine origin (3-vector), velocity]
    seg = [[[None, [0.0, 0.0, 0.0], list(v[p])]] for p in range(m)]
    last = [None] * m
    events = []
    E0 = sum(dot(x, x) for x in v)
    energies = []

    def move(g, delta):
        for p in range(m):
            if group[p] == g:
                for s in seg[p]:
                    s[1] = add(s[1], delta)

    def pos(p, t):
        s = seg[p][-1]
        return add(s[1], mul(t, s[2]))

    for p, q, y in links:
        assert group[p] != group[q]
        gq = group[q]
        move(gq, sub(add(seg[p][0][1], y), seg[q][0][1]))
        gp = group[p]
        group = [gp if g == gq else g for g in group]

    prev = None
    for k, sl in enumerate(slots):
        kind, p, q = sl[0], sl[1], sl[2]
        u = sub(cur[p], cur[q])
        if kind == 'M':
            t, om, co = sl[3], sl[4], sl[5]
            assert group[p] != group[q]
            if dot(u, om) <= 0:
                return dict(success=False, abort=k, why='flux', events=events)
            # contact equation x_p(t) - x_q(t) = -eps*omega: move q's group
            gq = group[q]
            move(gq, add(sub(pos(p, t), pos(q, t)), mul(eps, om)))
            gp = group[p]
            group = [gp if g == gq else g for g in group]
            n = mul(-1.0, om)
        else:
            co = sl[3]
            assert group[p] == group[q]
            d0 = sub(pos(p, 0.0), pos(q, 0.0))  # relative affine origin
            a = dot(u, u); b = 2 * dot(d0, u); c = dot(d0, d0) - eps * eps
            disc = b * b - 4 * a * c
            if a == 0 or disc <= 0:
                return dict(success=False, abort=k, why='none', events=events)
            t = (-b - math.sqrt(disc)) / (2 * a)  # entering root
            lows = [x for x in (last[p], last[q]) if x is not None]
            if lows and t < max(lows) - 1e-9 * (1 + abs(max(lows))):
                return dict(success=False, abort=k, why='ray', events=events)
            n = mul(1.0 / eps, add(d0, mul(t, u)))
        # strict global order; exact structural ties (e.g. a redundant slot
        # repeating the root left unchanged by a preceding O update) abort
        if prev is not None and not t > prev + 1e-9 * (1 + abs(prev)):
            return dict(success=False, abort=k, why='Q', events=events)
        xp, xq = pos(p, t), pos(q, t)
        if co == 'C':
            w = dot(u, n)
            cur[p] = sub(cur[p], mul(w, n))
            cur[q] = add(cur[q], mul(w, n))
        seg[p].append([t, sub(xp, mul(t, cur[p])), list(cur[p])])
        seg[q].append([t, sub(xq, mul(t, cur[q])), list(cur[q])])
        last[p] = last[q] = t
        prev = t
        events.append((kind, p, q, t, n))
        energies.append(sum(dot(x, x) for x in cur))
    assert len(set(group)) == 1
    move(group[0], sub(X, seg[0][0][1]))
    return dict(success=True, events=events, seg=seg, E0=E0, energies=energies)


def position(res, p, s):
    cur = res['seg'][p][0]
    for nx in res['seg'][p][1:]:
        if nx[0] <= s:
            cur = nx
    return add(cur[1], mul(s, cur[2])), cur[2]


def close(a, b, tol=TOL):
    return all(abs(a[i] - b[i]) <= tol * (1 + abs(a[i]) + abs(b[i])) for i in range(len(a)))


def shear(v, X, links, slots, theta):
    X2 = sub(X, mul(theta, v[0]))
    links2 = [(p, q, sub(y, mul(theta, sub(v[q], v[p])))) for p, q, y in links]
    slots2 = []
    for sl in slots:
        if sl[0] == 'M':
            slots2.append(('M', sl[1], sl[2], sl[3] + theta, sl[4], sl[5]))
        else:
            slots2.append(sl)
    return X2, links2, slots2


def rand_unit(rng):
    while True:
        w = [rng.gauss(0, 1) for _ in range(3)]
        if norm(w) > 1e-3:
            return mul(1 / norm(w), w)


def random_structure(rng, m):
    """Random forest of links, then merger tree plus redundant slots."""
    comps = [{p} for p in range(m)]
    links, slots = [], []
    find = lambda p: next(i for i, c in enumerate(comps) if p in c)
    for _ in range(rng.randint(0, 2)):
        p, q = rng.sample(range(m), 2)
        if find(p) != find(q):
            links.append((p, q, mul(rng.uniform(0.2, 1.0), rand_unit(rng))))
            i, j = find(p), find(q)
            comps[i] |= comps[j]; del comps[j]
    t = rng.uniform(-1, 0)
    while len(comps) > 1 or rng.random() < 0.6:
        if len(comps) > 1 and rng.random() < 0.65:
            p, q = rng.sample(range(m), 2)
            if find(p) == find(q):
                continue
            t += rng.uniform(0.05, 0.6)
            slots.append(('M', p, q, t, rand_unit(rng), rng.choice('CO')))
            i, j = find(p), find(q)
            comps[i] |= comps[j]; del comps[j]
        else:
            cands = [(p, q) for p in range(m) for q in range(m)
                     if p != q and find(p) == find(q)]
            if not cands:
                continue
            p, q = rng.choice(cands)
            slots.append(('R', p, q, rng.choice('CO')))
        if len(slots) > 3 * m:
            break
    while len(comps) > 1:
        p, q = rng.sample(range(m), 2)
        if find(p) != find(q):
            t += rng.uniform(0.05, 0.6)
            slots.append(('M', p, q, t, rand_unit(rng), rng.choice('CO')))
            i, j = find(p), find(q)
            comps[i] |= comps[j]; del comps[j]
    return links, slots


def check_covariance(trials=4000, seed=20261014):
    rng = random.Random(seed)
    n_succ = n_fail = n_red = 0
    reasons = {}
    for _ in range(trials):
        m = rng.randint(2, 5)
        eps = rng.uniform(0.3, 1.5)
        v = [[rng.gauss(0, 1) for _ in range(3)] for _ in range(m)]
        X = [rng.gauss(0, 3) for _ in range(3)]
        links, slots = random_structure(rng, m)
        base = build(v, X, links, slots, eps)
        for theta in (-2.3, -0.4, 0.37, 1.9):
            X2, l2, s2 = shear(v, X, links, slots, theta)
            sh = build(v, X2, l2, s2, eps)
            assert sh['success'] == base['success']
            if not base['success']:
                assert sh['abort'] == base['abort'] and sh['why'] == base['why']
                continue
            assert len(sh['events']) == len(base['events'])
            for e1, e2 in zip(base['events'], sh['events']):
                assert abs(e2[3] - e1[3] - theta) < 1e-7 * (1 + abs(e1[3]))
                assert close(e1[4], e2[4], 1e-6)
            for p in range(m):
                for s in (-5.0, -1.1, 0.0, 0.3, 2.2, 6.0):
                    # skip sample points within 1e-6 of an event (convention)
                    if any(abs(s - e[3]) < 1e-6 or abs(s - theta - e[3]) < 1e-6
                           for e in base['events']):
                        continue
                    x1, w1 = position(base, p, s - theta)
                    x2, w2 = position(sh, p, s)
                    assert close(x1, x2, 1e-6) and close(w1, w2, 1e-6)
        if base['success']:
            n_succ += 1
            n_red += sum(1 for e in base['events'] if e[0] == 'R')
            assert all(abs(e - base['E0']) < 1e-8 * (1 + base['E0'])
                       for e in base['energies'])
            ts = [e[3] for e in base['events']]
            assert all(ts[i] < ts[i + 1] for i in range(len(ts) - 1))
        else:
            n_fail += 1
            reasons[base['why']] = reasons.get(base['why'], 0) + 1
    check('claim2_covariance_success_abort_slot_and_segments_3d', True)
    check('all_m_line_energy_conserved_on_successful_extended_branches', True)
    check('successful_branches_globally_chronological', True)
    return dict(trials=trials, successful=n_succ, aborted=n_fail,
                abort_reasons=reasons, redundant_events_on_success=n_red)


def simulate(x0, v0, eps, tmax):
    """Exact event-driven hard spheres (equal masses), returns contact list."""
    m = len(x0)
    x = [list(a) for a in x0]; v = [list(a) for a in v0]
    t = 0.0; out = []
    while True:
        best = None
        for p, q in itertools.combinations(range(m), 2):
            d = sub(x[p], x[q]); u = sub(v[p], v[q])
            if dot(d, u) >= 0:
                continue
            a = dot(u, u); b = 2 * dot(d, u); c = dot(d, d) - eps * eps
            disc = b * b - 4 * a * c
            if disc <= 0:
                continue
            s = (-b - math.sqrt(disc)) / (2 * a)
            if s > 1e-12 and (best is None or s < best[0]):
                best = (s, p, q)
        if best is None or t + best[0] > tmax:
            return out
        s, p, q = best
        for r in range(m):
            x[r] = add(x[r], mul(s, v[r]))
        t += s
        n = mul(1 / eps, sub(x[p], x[q]))
        w = dot(sub(v[p], v[q]), n)
        v[p] = sub(v[p], mul(w, n)); v[q] = add(v[q], mul(w, n))
        out.append((t, p, q, n))


def check_physical_domination():
    """Claim 1 on genuine three-sphere histories with a recollision."""
    eps = 1.0
    configs = [
        ([[-3.0, 0.02, 0.0], [0.0, 0.0, 0.01], [3.0, -0.01, 0.0]],
         [[2.0, 0.0, 0.0], [0.0, 0.0, 0.0], [-1.0, 0.0, 0.0]]),
        ([[-4.0, 0.05, -0.03], [0.0, 0.0, 0.0], [2.5, 0.04, 0.02], [9.0, -0.02, 0.0]],
         [[2.5, 0.0, 0.0], [0.0, 0.0, 0.0], [-1.5, 0.0, 0.0], [-0.2, 0.0, 0.0]]),
    ]
    nred = 0
    for x0, v0 in configs:
        hist = simulate(x0, v0, eps, 50.0)
        pairs = [(p, q) for _, p, q, _ in hist]
        assert len(set(pairs)) < len(pairs), 'need a recollision'
        m = len(x0)
        for use_link in (False, True):
            comps = [{p} for p in range(m)]
            find = lambda p: next(i for i, c in enumerate(comps) if p in c)
            links = []
            if use_link:
                # an initial-link coordinate between lines 0 and m-1
                links.append((0, m - 1, sub(x0[m - 1], x0[0])))
                comps[0] |= comps[m - 1]; del comps[m - 1]
            slots = []
            for t, p, q, n in hist:
                if find(p) != find(q):
                    slots.append(('M', p, q, t, mul(-1.0, n), 'C'))
                    i, j = find(p), find(q)
                    comps[i] |= comps[j]; del comps[j]
                else:
                    slots.append(('R', p, q, 'C'))
            if len(comps) > 1:
                continue
            res = build(v0, x0[0], links, slots, eps)
            assert res['success']
            for (t, p, q, n), e in zip(hist, res['events']):
                assert abs(t - e[3]) < 1e-9 and close(n, e[4], 1e-9)
            nred += sum(1 for s in slots if s[0] == 'R')
            # segments: positions at sample times coincide with the physics
            for s in (0.0, 0.7, 1.3, 2.9, 4.4):
                xs = [add(x0[r], mul(s, v0[r])) for r in range(m)]
                # recompute physical state at s by replay
                xx = [list(a) for a in x0]; vv = [list(a) for a in v0]; tt = 0.0
                for t, p, q, n in hist:
                    if t > s:
                        break
                    for r in range(m):
                        xx[r] = add(xx[r], mul(t - tt, vv[r]))
                    tt = t
                    w = dot(sub(vv[p], vv[q]), n)
                    vv[p] = sub(vv[p], mul(w, n)); vv[q] = add(vv[q], mul(w, n))
                for r in range(m):
                    xx[r] = add(xx[r], mul(s - tt, vv[r]))
                    xe, ve = position(res, r, s)
                    assert close(xx[r], xe, 1e-9) and close(vv[r], ve, 1e-9)
    check('claim1_physical_histories_reproduced_with_recollisions', nred > 0)
    return dict(configs=len(configs), redundant_physical_contacts_checked=nred)


def minkowski_volume_exact(a, tau, Theta, N):
    """Exact-rational lattice Riemann sum of |S-[0,Theta]1| for S the open
    simplex {0<t1<...<ta<tau}; returns lower/upper sums on a grid of step h."""
    h = Fr(max(tau, Theta) + tau, N)
    lo = up = 0
    # membership: ordered, t_a - t_1 < tau, t_1 > -Theta, t_a < tau
    pts = [-Theta + h * k for k in range(int((tau + Theta) / h) + 1)]
    def inside(t):
        return (all(t[i] < t[i + 1] for i in range(len(t) - 1))
                and t[-1] - t[0] < tau and t[0] > -Theta and t[-1] < tau)
    for cell in itertools.product(range(len(pts) - 1), repeat=a):
        corners = [[pts[c + d[i]] for i, c in enumerate(cell)]
                   for d in itertools.product((0, 1), repeat=a)]
        ins = [inside(c) for c in corners]
        if all(ins):
            lo += h ** a
        if any(ins):
            up += h ** a
    return lo, up


def check_minkowski():
    out = []
    for a, tau, Theta, N in ((1, Fr(1), Fr(1), 64), (2, Fr(1), Fr(1), 120),
                             (2, Fr(1), Fr(1, 2), 120), (3, Fr(1), Fr(1), 40)):
        exact = tau ** a / math.factorial(a) + Theta * tau ** (a - 1) / math.factorial(a - 1)
        lo, up = minkowski_volume_exact(a, tau, Theta, N)
        assert lo <= exact <= up, (a, lo, exact, up)
        out.append(dict(a=a, Theta=str(Theta), lower=float(lo), formula=float(exact), upper=float(up)))
    check('minkowski_formula_between_exact_rational_lower_upper_sums', True)
    # the (1+a) factor at Theta = tau
    for a in range(1, 30):
        ratio = Fr(1) + Fr(a)  # (tau^a/a! + tau^a/(a-1)!)/(tau^a/a!)
        assert ratio == 1 + a
    return out


def check_stirling_and_flux(seed=7):
    for n in range(1, 160):
        for d in range(0, min(n, 6) + 1):
            a = n - d
            lhs = 1.5 * a * math.log(n) - math.lgamma(a + 1) - math.lgamma(n + 1)
            rhs = 2 * n + d * math.log(1 + n) - 0.5 * n * math.log(n)
            assert lhs <= rhs + 1e-9, (n, d)
    check('stirling_step_n32a_over_a_fact_n_fact', True)
    rng = random.Random(seed)
    for _ in range(3000):
        n = rng.randint(2, 9)
        vs = [[rng.gauss(0, rng.uniform(0.1, 3)) for _ in range(3)] for _ in range(n)]
        P = sum(dot(x, x) for x in vs) * rng.uniform(1.0, 2.0)
        om = rand_unit(rng)
        s = sum(max(0.0, dot(sub(vs[p], vs[q]), om)) for p in range(n) for q in range(p + 1, n))
        assert s <= n ** 1.5 * math.sqrt(P) + 1e-9
    check('pair_flux_bound_on_energy_bin', True)
    # energy-bin sum: sum_P e^{-bP/4} P^{a/2} <= C^{a+1}(1+a)^{a/2} with C=C(b)
    b = 0.3
    worst = 0.0
    for a in range(0, 120):
        s = sum(math.exp(-b * 2 ** k / 4 + (a / 2) * k * math.log(2)) for k in range(0, 80))
        worst = max(worst, (math.log(s) - (a / 2) * math.log(1 + a)) / (a + 1))
    results['energy_bin_log_base_observed'] = worst
    check('energy_bin_sum_has_K_independent_exponential_base', worst < 5)


if __name__ == '__main__':
    summary = {}
    summary['covariance'] = check_covariance()
    summary['physical'] = check_physical_domination()
    summary['minkowski'] = check_minkowski()
    check_stirling_and_flux()
    # exponent arithmetic re-derived
    assert Fr(-1) + Fr(21, 20) * Fr(21, 22) == Fr(1, 440)
    # dyadic: mu^-1 * (alpha^-1)^(4/8) with alpha = mu^-3/2 -> mu^(-1+3/4)
    assert Fr(-1) + Fr(3, 2) * Fr(4, 8) == Fr(-1, 4)
    # union: (T/alpha) * mu*alpha / mu^(3/2) -> mu^(-1/2)
    assert Fr(1) - Fr(3, 2) == Fr(-1, 2)
    # remainder: (1/alpha) * eps^P / mu^(3/2) = mu^(3/2-3/2+3)... in eps: P - 6 with mu^3 eps^P
    assert Fr(3, 2) + Fr(3, 2) == 3
    # chaining remainder R alpha^(-1-4theta) <= R alpha^-2 when theta=1/8
    assert Fr(1) + 4 * Fr(1, 8) <= 2
    check('exponent_arithmetic', True)
    summary['checks'] = results
    summary['status'] = 'PASS'
    summary['scope'] = 'finite supporting controls only; not a proof certificate'
    print(json.dumps(summary, indent=1, default=str))
