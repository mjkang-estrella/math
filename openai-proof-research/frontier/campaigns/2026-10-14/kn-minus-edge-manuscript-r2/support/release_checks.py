#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License (see LICENSE-CODE).
"""Release checks for the manuscript on cr(K_n - e).

Python 3 standard library only. Integer arithmetic uses //, rational arithmetic
uses fractions.Fraction; no floating point is used anywhere in this file.
Every check is enforced: a failure is recorded, printed, and makes the process
exit with status 1. Python's -O flag cannot disable these checks.

These are finite checks of identities, bookkeeping and hypotheses used in the
proof. They are not a proof of the all-n theorem.
"""
import itertools
import json
import random
import sys
import time
from fractions import Fraction as Fr
from math import comb
from pathlib import Path

FAILURES = []
COUNTS = {}


def check(group, condition, detail):
    COUNTS[group] = COUNTS.get(group, 0) + 1
    if not condition:
        FAILURES.append(f"{group}: {detail}")
        print(f"FAIL {group}: {detail}", flush=True)


def Z(n):
    return (n // 2) * ((n - 1) // 2) * ((n - 2) // 2) * ((n - 3) // 2) // 4


def target(n):
    return Z(n) - comb((n - 1) // 2, 2)


def floor_product(n):
    return ((n + 2) // 2) * ((n - 1) // 2) * ((n - 3) // 2) * ((n - 4) // 2)


# R1 -------------------------------------------------------------------------
def r1_closed_forms(limit=3000):
    for n in range(2, limit + 1):
        prod4 = (n // 2) * ((n - 1) // 2) * ((n - 2) // 2) * ((n - 3) // 2)
        check("R1", prod4 % 4 == 0, f"Z({n}) numerator not divisible by 4")
        check("R1", 4 * target(n) == floor_product(n), f"floor product n={n}")
        s = n // 2
        if n % 2 == 1:
            check("R1", target(n) == comb(s, 2) ** 2 - comb(s, 2), f"odd parity n={n}")
        else:
            check("R1", target(n) == comb(s, 2) * comb(s - 1, 2) - comb(s - 1, 2), f"even parity n={n}")
            check("R1", 4 * target(n) == (s * s - 1) * (s - 2) ** 2, f"even closed n={n}")
        if n <= 5:
            check("R1", target(n) == 0, f"small n={n}")


# R2 -------------------------------------------------------------------------
def r2_two_page_deletion(limit=56):
    for n in range(4, limit + 1):
        m = n // 2
        edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
        page = {e: ((e[0] + e[1]) % n) < m for e in edges}
        per_edge = {e: 0 for e in edges}
        total = 0
        for (i, j), (k, l) in itertools.combinations(edges, 2):
            if page[(i, j)] != page[(k, l)] or len({i, j, k, l}) < 4:
                continue
            if (i < k < j < l) or (k < i < l < j):
                total += 1
                per_edge[(i, j)] += 1
                per_edge[(k, l)] += 1
        t = (n - 1) // 2
        check("R2", total == Z(n), f"two-page total n={n}")
        check("R2", per_edge[(0, t)] == comb(t, 2), f"edge (0,{t}) count n={n}")
        check("R2", total - per_edge[(0, t)] == target(n), f"deleted drawing n={n}")


# R3 -------------------------------------------------------------------------
def r3_even_identity(limit=3000):
    for n in range(6, limit + 1, 2):
        check("R3", (n + 2) * Z(n - 1) == (n - 2) * target(n), f"even identity n={n}")


# R4 -------------------------------------------------------------------------
def ceil_div(a, b):
    return -((-a) // b)


def r4_routine_range(limit=401):
    closes = []
    for n in range(5, limit + 1, 2):
        s = (n - 1) // 2
        numerator = 2 * Z(n - 1) + (n - 2) * (Z(n) - (n - 3) // 2)
        bound = Fr(numerator, n)
        deficit = Fr(target(n)) - bound
        check("R4", deficit == Fr((s - 1) * (s - 2), 2 * (2 * s + 1)), f"OWH 3.1 deficit n={n}")
        check("R4", (s - 1) * (s - 2) - 2 * (2 * s + 1) == s * (s - 7), f"deficit sign n={n}")
        if ceil_div(numerator, n) == target(n):
            closes.append(n)
        if s >= 3:
            # OWH Theorem 3.2 at odd order.
            gap32 = Fr(target(n)) - Fr((n + 2) * Z(n - 1), n - 2)
            check("R4", gap32 == Fr(s * (s - 1) * (s - 2), 2 * (2 * s - 1)), f"OWH 3.2 gap n={n}")
            # Vertex-deletion average: ends of the missing edge charged Z(2s), others target(2s).
            avg_num, avg_den = 2 * Z(2 * s) + (2 * s - 1) * target(2 * s), 2 * s - 3
            gap_avg = Fr(target(n)) - Fr(avg_num, avg_den)
            check("R4", gap_avg == Fr((s - 1) ** 2 * (s - 2), 2 * (2 * s - 3)), f"vertex-average gap n={n}")
            if n >= 15:
                check("R4", ceil_div((n + 2) * Z(n - 1), n - 2) < target(n), f"OWH 3.2 below target n={n}")
                check("R4", ceil_div(avg_num, avg_den) < target(n), f"vertex average below target n={n}")
    check("R4", closes == [5, 7, 9, 11, 13], f"integrality closes exactly {closes}")
    check("R4", ceil_div(2 * Z(14) + 13 * (Z(15) - 6), 15) == 419, "n=15 ceiling 419")
    check("R4", Fr(2 * Z(12) + 11 * (Z(13) - 5), 13) == Fr(2720, 13), "n=13 bound 2720/13")


# R5 -------------------------------------------------------------------------
def zheng_times4(m, n):
    return ((m + 1) // 2) * ((m - 1) // 2) * ((m - 2) // 2) * (n * ((m + 4) // 2) + (m - 4) // 2)


def r5_corollary(m_limit=400, n_limit=12):
    for m in range(4, m_limit + 1):
        for n in range(1, n_limit + 1):
            lhs4 = 4 * ((n - 1) * target(m + 2) + 2 * Z(m + 1))
            check("R5", lhs4 == zheng_times4(m, n), f"Corollary B m={m} n={n}")
    check("R5", all((n - 1) * target(6) + 2 * Z(5) == 2 * n for n in range(1, 50)), "m=4 gives 2n")


# exact linear algebra ---------------------------------------------------------
def rank(rows):
    rows = [list(r) for r in rows]
    if not rows:
        return 0
    ncols = len(rows[0])
    r = 0
    for c in range(ncols):
        pivot = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        inv = 1 / Fr(rows[r][c])
        rows[r] = [x * inv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [a - f * b for a, b in zip(rows[i], rows[r])]
        r += 1
        if r == len(rows):
            break
    return r


def distinct_nodes(rng, count):
    nodes = set()
    while len(nodes) < count:
        nodes.add(Fr(rng.randint(-60, 60), rng.randint(1, 7)))
    nodes = list(nodes)
    rng.shuffle(nodes)
    return nodes


# R6 -------------------------------------------------------------------------
def order_pairing(nodes, order_pos, product):
    """M(A,B) from upstream eq:M, with the product AB supplied as a function."""
    total = Fr(0)
    gp = []
    for p, up in enumerate(nodes):
        d = Fr(1)
        for q, uq in enumerate(nodes):
            if q != p:
                d *= up - uq
        gp.append(d)
    for p, up in enumerate(nodes):
        for q, uq in enumerate(nodes):
            if p == q:
                continue
            sign = Fr(1, 2) if order_pos[p] < order_pos[q] else Fr(-1, 2)
            total += sign * (up - uq) / (gp[p] * gp[q]) * product(up, uq)
    return total


def monomials(a, b):
    return [(i, j) for i in range(a + 1) for j in range(b + 1)]


def r6_twisted_detector(rng, s_max=5, trials=2):
    for s in range(2, s_max + 1):
        for _ in range(trials):
            nodes = distinct_nodes(rng, 2 * s)
            perm = list(range(2 * s))
            rng.shuffle(perm)
            order_pos = {node_index: position for position, node_index in enumerate(perm)}
            # Upstream U4 instance: rectangle pairing nonsingular (sanity check of the premise).
            rect = [[order_pairing(nodes, order_pos,
                                   lambda u, v, a=a, b=b: u ** (a[0] + b[0]) * v ** (a[1] + b[1]))
                     for b in monomials(s - 2, s - 1)] for a in monomials(s - 1, s - 2)]
            check("R6", rank(rect) == s * (s - 1), f"U4 instance s={s}")
            for c in range(2 * s):
                uc = nodes[c]
                rows = [[order_pairing(nodes, order_pos,
                                       lambda u, v, a=a, b=b: u ** (a[0] + b[0]) * v ** (a[1] + b[1]) * (v - uc))
                         for b in monomials(s - 1, s - 2)] for a in monomials(s - 2, s - 2)]
                check("R6", rank(rows) == (s - 1) ** 2, f"twisted detector s={s} c={c}")


# sparse polynomials in (x,u,y,v) --------------------------------------------
def padd(*polys):
    out = {}
    for poly in polys:
        for k, v in poly.items():
            out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v != 0}


def pmul(*polys):
    out = {(0, 0, 0, 0): Fr(1)}
    for poly in polys:
        new = {}
        for k1, v1 in out.items():
            for k2, v2 in poly.items():
                k = tuple(a + b for a, b in zip(k1, k2))
                new[k] = new.get(k, 0) + v1 * v2
        out = {k: v for k, v in new.items() if v != 0}
    return out


def pscale(poly, c):
    return {k: v * c for k, v in poly.items() if v * c != 0}


def var(i):
    e = [0, 0, 0, 0]
    e[i] = 1
    return {tuple(e): Fr(1)}


def const(c):
    return {(0, 0, 0, 0): Fr(c)} if c != 0 else {}


def lin(i, c):
    """variable i minus constant c"""
    return padd(var(i), const(-c))


X, U, Y, V = 0, 1, 2, 3


def substitute(poly, assignments):
    """Substitute constants for some variables; returns polynomial in the rest."""
    out = {}
    for k, v in poly.items():
        coeff = v
        key = list(k)
        for i, value in assignments.items():
            coeff *= Fr(value) ** k[i]
            key[i] = 0
        key = tuple(key)
        out[key] = out.get(key, 0) + coeff
    return {k: v for k, v in out.items() if v != 0}


def degrees(poly):
    return tuple(max((k[i] for k in poly), default=-1) for i in range(4))


def sym_pair(rng, d, first, second):
    """random polynomial symmetric in variables (first, second), degree <= d in each"""
    poly = {}
    for a in range(d + 1):
        for b in range(a, d + 1):
            c = Fr(rng.randint(-5, 5))
            if c == 0:
                continue
            for (p, q) in {(a, b), (b, a)}:
                e = [0, 0, 0, 0]
                e[first] += p
                e[second] += q
                poly = padd(poly, {tuple(e): c})
    return poly


def random_Sa(rng, s, ta, tb, terms=3):
    """sum of (q1(x,u)-q1(ta,tb)) q2(y,v): spans S_a"""
    total = {}
    for _ in range(terms):
        q1 = sym_pair(rng, s - 2, X, U)
        q2 = sym_pair(rng, s - 2, Y, V)
        shift = substitute(q1, {X: ta, U: tb})
        total = padd(total, pmul(padd(q1, pscale(shift, -1)), q2))
    return total


def swap_slots(poly):
    return {(k[2], k[3], k[0], k[1]): v for k, v in poly.items()}


def r7_dimensions(rng, s_max=6):
    for s in range(2, s_max + 1):
        d = comb(s, 2)
        ta, tb = distinct_nodes(rng, 2)
        pairs = [(a, b) for a in range(s - 1) for b in range(a, s - 1)]

        def sym_value(pair, x, u):
            a, b = pair
            return x ** a * u ** b + (x ** b * u ** a if a != b else 0)

        # S = Sym (x) Sym; coordinates (p1, p2). Condition for S_a: for each p2,
        # sum_{p1} c[p1,p2] sym_value(p1, ta, tb) = 0.
        basis = [(p1, p2) for p1 in pairs for p2 in pairs]
        cond_a = [[sym_value(p1, ta, tb) if p2 == q2 else 0 for (p1, p2) in basis] for q2 in pairs]
        cond_b = [[sym_value(p2, ta, tb) if p1 == q1 else 0 for (p1, p2) in basis] for q1 in pairs]
        check("R7", len(basis) == d * d, f"dim S s={s}")
        check("R7", len(basis) - rank(cond_a) == d * d - d, f"dim S_a s={s}")
        check("R7", len(basis) - rank(cond_b) == d * d - d, f"dim S_b s={s}")
        both = len(basis) - rank(cond_a + cond_b)
        check("R7", both == d * d - 2 * d + 1, f"dim S_a cap S_b s={s}")
        check("R7", (d * d - d) - both == d - 1, f"intersection shortfall s={s}")


def r8_test_hypotheses(rng, s_min=3, s_max=7):
    for s in range(s_min, s_max + 1):
        n = 2 * s + 1
        ta, tb = distinct_nodes(rng, 2)
        P = random_Sa(rng, s, ta, tb)
        Q = swap_slots(random_Sa(rng, s, ta, tb))
        check("R8", P != {} and Q != {}, f"nonzero samples s={s}")
        check("R8", all(d <= s - 2 for d in degrees(P)), f"P degrees s={s}")
        check("R8", substitute(P, {X: ta, U: tb}) == {} and substitute(P, {X: tb, U: ta}) == {},
              f"P in S_a s={s}")
        check("R8", substitute(Q, {Y: ta, V: tb}) == {} and substitute(Q, {Y: tb, V: ta}) == {},
              f"Q in S_b s={s}")
        check("R8", P == {(k[1], k[0], k[2], k[3]): v for k, v in P.items()}, f"P x<->u symmetric s={s}")
        check("R8", P == {(k[0], k[1], k[3], k[2]): v for k, v in P.items()}, f"P y<->v symmetric s={s}")

        delta = pmul(padd(var(X), pscale(var(U), -1)), padd(var(Y), pscale(var(V), -1)),
                     padd(var(X), pscale(var(Y), -1)), padd(var(X), pscale(var(V), -1)),
                     padd(var(U), pscale(var(Y), -1)), padd(var(U), pscale(var(V), -1)))
        iso = pmul(P, Q, delta)
        check("R8", all(d <= n - 2 for d in degrees(iso)), f"isotropy degrees s={s}: {degrees(iso)}")
        for assign in ({X: ta, U: tb}, {X: tb, U: ta}, {Y: ta, V: tb}, {Y: tb, V: ta}):
            check("R8", substitute(iso, assign) == {}, f"isotropy test missing-pair identity s={s}")

        # Negative control: a generic P from S (not S_a) breaks the first-slot identity.
        P_generic = pmul(sym_pair(rng, s - 2, X, U), sym_pair(rng, s - 2, Y, V))
        bad = pmul(P_generic, Q, delta)
        check("R8", substitute(bad, {X: ta, U: tb}) != substitute(bad, {X: tb, U: ta}),
              f"control: generic S element violates first-slot symmetry s={s}")

        # Localization test of Lemma 3.5(a)
        Upoly = {(i, 0, 0, 0): Fr(rng.randint(1, 5)) for i in range(s + 1)}
        Vprime = {(0, 0, i, 0): Fr(rng.randint(1, 5)) for i in range(s)}
        Bprime = {(0, i, 0, j): Fr(rng.randint(1, 5)) for i in range(s) for j in range(s - 1)}
        common = [P, padd(var(U), pscale(var(V), -1)), padd(var(U), pscale(var(Y), -1)),
                  padd(var(V), pscale(var(X), -1)), Upoly, Vprime, Bprime]
        H = pmul(*common, lin(Y, ta), lin(V, ta))
        check("R8", degrees(H) == (n - 2,) * 4, f"localization degrees exactly n-2 s={s}: {degrees(H)}")
        for assign in ({X: ta, U: tb}, {X: tb, U: ta}, {Y: ta, V: tb}, {Y: tb, V: ta}):
            check("R8", substitute(H, assign) == {}, f"localization missing-pair identity s={s} {assign}")
        # Negative controls: each twist factor is needed for one substitution.
        no_y = pmul(*common, lin(V, ta))
        no_v = pmul(*common, lin(Y, ta))
        check("R8", substitute(no_y, {Y: ta, V: tb}) != {}, f"control: (y-t_a) omitted s={s}")
        check("R8", substitute(no_v, {Y: tb, V: ta}) != {}, f"control: (v-t_a) omitted s={s}")
        # Upstream untwisted localization test (V of degree s, B in P_{s-1,s-1}) is inadmissible.
        Vfull = {(0, 0, i, 0): Fr(rng.randint(1, 5)) for i in range(s + 1)}
        Bfull = {(0, i, 0, j): Fr(rng.randint(1, 5)) for i in range(s) for j in range(s)}
        upstream = pmul(*common[:5], Vfull, Bfull)
        check("R8", substitute(upstream, {Y: ta, V: tb}) != substitute(upstream, {Y: tb, V: ta}),
              f"control: upstream localization test violates second-slot symmetry s={s}")

        # Isolation: products U(t)(t-t_a)V'(t) span all polynomials of degree <= 2s vanishing at t_a.
        rows = []
        for i in range(s + 1):
            for j in range(s):
                coeffs = [Fr(0)] * (2 * s + 1)
                coeffs[i + j + 1] += 1
                coeffs[i + j] -= ta
                rows.append(coeffs)
        check("R8", rank(rows) == 2 * s, f"isolation span s={s}")


def r9_orientation_and_nonconverse(rng, n_values=(7, 9)):
    """Random skew forms (not drawings): bookkeeping and the H=xy non-converse."""
    for n in n_values:
        s = (n - 1) // 2
        a, b = 0, 1
        t = distinct_nodes(rng, n)
        w = []
        for i in range(n):
            d = Fr(1)
            for j in range(n):
                if j != i:
                    d *= t[i] - t[j]
            w.append(1 / d)
        edges = [(i, p) for i in range(n) for p in range(i + 1, n) if {i, p} != {a, b}]
        index = {e: k for k, e in enumerate(edges)}
        J = [[Fr(0)] * len(edges) for _ in edges]
        for e1 in range(len(edges)):
            for e2 in range(e1 + 1, len(edges)):
                value = Fr(rng.randint(-3, 3), 2)
                J[e1][e2], J[e2][e1] = value, -value

        def Jo(i, p, k, q):
            if i == p or k == q:
                return Fr(0)
            s1, e1 = (1, (i, p)) if i < p else (-1, (p, i))
            s2, e2 = (1, (k, q)) if k < q else (-1, (q, k))
            if e1 not in index or e2 not in index:
                return Fr(0)
            return s1 * s2 * J[index[e1]][index[e2]]

        def full_sum(h):
            total = Fr(0)
            for i, p, k, q in itertools.product(range(n), repeat=4):
                j = Jo(i, p, k, q)
                if j:
                    total += j * w[i] * w[p] * w[k] * w[q] * h(t[i], t[p], t[k], t[q])
            return total

        # Non-converse: H = xy violates both identities but its sum is J(z,z) = 0.
        check("R9", t[a] != t[b], "distinct missing labels")
        xy = pmul(var(X), var(Y))
        check("R9", substitute(xy, {X: t[a], U: t[b]}) != substitute(xy, {X: t[b], U: t[a]})
              and substitute(xy, {Y: t[a], V: t[b]}) != substitute(xy, {Y: t[b], V: t[a]}),
              f"H=xy violates both missing-pair identities n={n}")
        check("R9", full_sum(lambda x, u, y, v: x * y) == 0, f"H=xy sum vanishes n={n}")
        # Orientation bookkeeping: full ordered sum equals 4 x sum over ordered pairs of
        # undirected independent edges, for P in S_a, Q in S_b (any skew J).
        P = random_Sa(rng, s, t[a], t[b], terms=2)
        Q = swap_slots(random_Sa(rng, s, t[a], t[b], terms=2))

        def ev(poly, vals):
            total = Fr(0)
            for k, v in poly.items():
                total += v * vals[0] ** k[0] * vals[1] ** k[1] * vals[2] ** k[2] * vals[3] ** k[3]
            return total

        def delta(x, u, y, v):
            return (x - u) * (y - v) * (x - y) * (x - v) * (u - y) * (u - v)

        h = lambda x, u, y, v: ev(P, (x, u, y, v)) * ev(Q, (x, u, y, v)) * delta(x, u, y, v)
        full = full_sum(h)
        diag = Fr(0)
        for e, f in itertools.product(edges, repeat=2):
            if len(set(e) | set(f)) < 4:
                continue
            alpha = J[index[e]][index[f]] * w[e[0]] * w[e[1]] * w[f[0]] * w[f[1]] * delta(t[e[0]], t[e[1]], t[f[0]], t[f[1]])
            diag += alpha * ev(P, (t[e[0]], t[e[1]], t[f[0]], t[f[1]])) * ev(Q, (t[e[0]], t[e[1]], t[f[0]], t[f[1]]))
        check("R9", full == 4 * diag, f"four-orientation factor n={n}")
        # Slot exchange: coefficient changes sign (J skew, Delta invariant).
        e, f = edges[2], edges[-1]
        if len(set(e) | set(f)) == 4:
            ae = J[index[e]][index[f]] * delta(t[e[0]], t[e[1]], t[f[0]], t[f[1]])
            af = J[index[f]][index[e]] * delta(t[f[0]], t[f[1]], t[e[0]], t[e[1]])
            check("R9", ae == -af, f"slot exchange sign n={n}")


def main():
    start = time.monotonic()
    rng = random.Random(20261016)
    steps = [("R1 closed forms n<=3000", r1_closed_forms),
             ("R2 two-page deletion count 4<=n<=56", r2_two_page_deletion),
             ("R3 even identity 6<=n<=3000", r3_even_identity),
             ("R4 OWH Thm 3.1 routine range, odd n<=401", r4_routine_range),
             ("R5 Corollary B substitution 4<=m<=400, 1<=n<=12", r5_corollary),
             ("R6 exact twisted detector ranks s<=5, every twist node", lambda: r6_twisted_detector(rng)),
             ("R7 exact dimensions of S_a, S_b, S_a cap S_b, s<=6", lambda: r7_dimensions(rng)),
             ("R8 test-polynomial hypotheses and enforced controls, 3<=s<=7", lambda: r8_test_hypotheses(rng)),
             ("R9 orientation factor and H=xy non-converse, n=7,9", lambda: r9_orientation_and_nonconverse(rng))]
    for label, step in steps:
        before = len(FAILURES)
        step()
        group = label.split()[0]
        status = "ok" if len(FAILURES) == before else "FAIL"
        print(f"{status} {label}: {COUNTS.get(group, 0)} assertions", flush=True)
    elapsed = time.monotonic() - start
    result = {"assertions": COUNTS, "failures": FAILURES, "status": "PASS" if not FAILURES else "FAIL",
              "seed": 20261016, "python": sys.version.split()[0], "runtime_seconds": round(elapsed, 1)}
    if len(sys.argv) > 1:
        Path(sys.argv[1]).write_text(json.dumps(result, indent=2) + "\n")
    if FAILURES:
        print(f"RELEASE CHECKS FAILED: {len(FAILURES)} failure(s)")
        sys.exit(1)
    print("RELEASE CHECKS PASSED")


if __name__ == "__main__":
    main()
