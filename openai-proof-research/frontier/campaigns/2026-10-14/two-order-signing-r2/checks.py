#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Exact finite checks for two-order-signing-r2 (standard library only).

These checks replay finite instances of the written proofs in candidate.md.
They are not proofs of the general statements, of T2, or of any novelty claim.
The script reads no files, writes no files and uses no network.
"""
import itertools
import random
import sys
from fractions import Fraction as F

SEED = 20261016
FAILS = []


def report(name, ok, detail):
    print(f"{name}: {'PASS' if ok else 'FAIL'} {detail}")
    if not ok:
        FAILS.append(name)


def vadd(a, b):
    return tuple(x + y for x, y in zip(a, b))


def vscale(c, a):
    return tuple(c * x for x in a)


def sqn(a):
    return sum(x * x for x in a)


def zero(d):
    return tuple(F(0) for _ in range(d))


def rand_ball_vector(rng, d):
    while True:
        v = tuple(F(rng.randint(-12, 12), 12) for _ in range(d))
        if sqn(v) <= 1:
            return v


def prefix_sums(order, vecs, eps, d):
    out = [zero(d)]
    s = zero(d)
    for i in order:
        s = vadd(s, vscale(eps[i], vecs[i]))
        out.append(s)
    return out


def max_sq_two_order(pi, rho, vecs, eps, d):
    return max(max(sqn(p) for p in prefix_sums(pi, vecs, eps, d)),
               max(sqn(p) for p in prefix_sums(rho, vecs, eps, d)))


def coverage(intervals, vecs, eps, x, d):
    s = zero(d)
    for j, (l, r) in enumerate(intervals):
        if l <= x <= r:
            s = vadd(s, vscale(eps[j], vecs[j]))
    return s


def all_signings(n):
    for bits in itertools.product((1, -1), repeat=n):
        yield bits


# ---------------------------------------------------------------- Check A1
def check_A1(rng):
    """Two orders -> one interval family; every prefix is a coverage value."""
    cases = 0
    signings = 0
    ok = True
    for _ in range(60):
        N = rng.randint(1, 7)
        d = rng.randint(1, 3)
        pi = list(range(N)); rng.shuffle(pi)
        rho = list(range(N)); rng.shuffle(rho)
        a = {pi[k]: k + 1 for k in range(N)}
        b = {rho[k]: k + 1 for k in range(N)}
        vecs = [rand_ball_vector(rng, d) for _ in range(N)]
        iv = [(F(a[i]), F(2 * N + 1 - b[i])) for i in range(N)]
        if any(l > r for l, r in iv):
            ok = False
        cases += 1
        for eps in all_signings(N):
            signings += 1
            pp = prefix_sums(pi, vecs, eps, d)
            pr = prefix_sums(rho, vecs, eps, d)
            for k in range(1, N + 1):
                if coverage(iv, vecs, eps, F(k), d) != pp[k]:
                    ok = False
                if coverage(iv, vecs, eps, F(2 * N + 1 - k), d) != pr[k]:
                    ok = False
            sup_cov = max(sqn(coverage(iv, vecs, eps, F(t, 2), d))
                          for t in range(0, 4 * N + 4))
            if max_sq_two_order(pi, rho, vecs, eps, d) > sup_cov:
                ok = False
    report("A1_two_orders_embed_in_interval_coverage", ok,
           f"cases={cases} signings={signings}")


# ---------------------------------------------------------------- Check A2
def check_A2(rng):
    """Interval coverage = left-endpoint prefix minus right-endpoint prefix,
    and the brute-force optimum obeys disc_I <= 2 disc_2 (squared: <= 4x)."""
    cases = 0
    pts = 0
    ok = True
    for _ in range(60):
        N = rng.randint(1, 7)
        d = rng.randint(1, 2)
        m = rng.randint(1, 9)
        iv = []
        for _ in range(N):
            l = rng.randint(1, m); r = rng.randint(l, m)
            iv.append((F(l), F(r)))
        vecs = [rand_ball_vector(rng, d) for _ in range(N)]
        sigL = sorted(range(N), key=lambda j: (iv[j][0], j))
        sigR = sorted(range(N), key=lambda j: (iv[j][1], j))
        cases += 1
        best_I = None
        best_2 = None
        for eps in all_signings(N):
            pl = prefix_sums(sigL, vecs, eps, d)
            pr = prefix_sums(sigR, vecs, eps, d)
            worst = F(0)
            for t in range(0, 2 * m + 3):
                x = F(t, 2)
                Lset = [j for j in range(N) if iv[j][0] <= x]
                Rset = [j for j in range(N) if iv[j][1] < x]
                # Lset/Rset are initial segments of the two orders
                if set(Lset) != set(sigL[:len(Lset)]) or set(Rset) != set(sigR[:len(Rset)]):
                    ok = False
                if not set(Rset) <= set(Lset):
                    ok = False
                cov = coverage(iv, vecs, eps, x, d)
                diff = vadd(pl[len(Lset)], vscale(-1, pr[len(Rset)]))
                if cov != diff:
                    ok = False
                worst = max(worst, sqn(cov))
                pts += 1
            two = max_sq_two_order(sigL, sigR, vecs, eps, d)
            best_I = worst if best_I is None else min(best_I, worst)
            best_2 = two if best_2 is None else min(best_2, two)
        if best_I > 4 * best_2:
            ok = False
    report("A2_interval_coverage_reduces_to_two_orders", ok,
           f"cases={cases} evaluated_points={pts}")


# ---------------------------------------------------------------- Check A3
def check_A3(rng):
    """Two-permutation prefix matrix is one-block after rows P1..PN,QN..Q1."""
    ok = True
    cases = 0
    for _ in range(200):
        N = rng.randint(1, 12)
        pi = list(range(N)); rng.shuffle(pi)
        rho = list(range(N)); rng.shuffle(rho)
        rows = [set(pi[:k]) for k in range(1, N + 1)] + \
               [set(rho[:k]) for k in range(N, 0, -1)]
        for j in range(N):
            col = [1 if j in r else 0 for r in rows]
            ones = [t for t, c in enumerate(col) if c]
            if not ones or ones != list(range(ones[0], ones[-1] + 1)):
                ok = False
        cases += 1
    report("A3_two_permutation_matrix_is_one_block", ok, f"cases={cases}")


# ---------------------------------------------------------------- Check M
def check_matroid(rng):
    """Partition-matroid prefix identity used in Proposition 3."""
    ok = True
    cases = 0
    bases = 0
    for _ in range(80):
        N = rng.randint(1, 7)
        pi = list(range(N)); rng.shuffle(pi)
        rho = list(range(N)); rng.shuffle(rho)
        w = [F(rng.randint(0, 10), 10) for _ in range(N)]
        tau = [(i, +1) for i in pi] + [(i, -1) for i in rho]
        cases += 1
        for delta in all_signings(N):
            bases += 1
            B = {(i, delta[i]) for i in range(N)}
            run = F(0)
            vals = []
            for (i, s) in tau:
                run += w[i] * ((1 if (i, s) in B else 0) - F(1, 2))
                vals.append(run)
            total = sum(w[i] * delta[i] for i in range(N))
            pp = F(0)
            for k in range(N):
                pp += w[pi[k]] * delta[pi[k]]
                if vals[k] != pp / 2:
                    ok = False
            qq = F(0)
            for k in range(N):
                qq += w[rho[k]] * delta[rho[k]]
                if vals[N + k] != total / 2 - qq / 2:
                    ok = False
            # the derived bounds: |pi-prefix| <= 2E, |rho-prefix| <= 4E
            E = max(abs(v) for v in vals)
            pref = F(0)
            for k in range(N):
                pref += w[pi[k]] * delta[pi[k]]
                if abs(pref) > 2 * E:
                    ok = False
            pref = F(0)
            for k in range(N):
                pref += w[rho[k]] * delta[rho[k]]
                if abs(pref) > 4 * E:
                    ok = False
    report("M_partition_matroid_embedding", ok, f"cases={cases} bases={bases}")


# ---------------------------------------------------------------- Check B
def nullspace_vector(rows, cols):
    """Return a nonzero rational vector y on `cols` with rows.y = 0, or None.
    rows: list of dicts col->coeff."""
    n = len(cols)
    if n == 0:
        return None
    idx = {c: t for t, c in enumerate(cols)}
    mat = []
    for r in rows:
        vec = [F(0)] * n
        nz = False
        for c, val in r.items():
            if c in idx and val != 0:
                vec[idx[c]] += val
                nz = True
        if nz:
            mat.append(vec)
    piv_cols = []
    rank = 0
    for c in range(n):
        p = None
        for rr in range(rank, len(mat)):
            if mat[rr][c] != 0:
                p = rr
                break
        if p is None:
            continue
        mat[rank], mat[p] = mat[p], mat[rank]
        pv = mat[rank][c]
        mat[rank] = [v / pv for v in mat[rank]]
        for rr in range(len(mat)):
            if rr != rank and mat[rr][c] != 0:
                f = mat[rr][c]
                mat[rr] = [a - f * b for a, b in zip(mat[rr], mat[rank])]
        piv_cols.append(c)
        rank += 1
        if rank == len(mat):
            break
    free = [c for c in range(n) if c not in piv_cols]
    if not free:
        return None
    fc = free[0]
    y = [F(0)] * n
    y[fc] = F(1)
    for rr, pc in enumerate(piv_cols):
        y[pc] = -mat[rr][fc]
    return {cols[t]: y[t] for t in range(n)}


def baseline_round(vecs, pi, rho, d):
    """Proposition 5 algorithm; returns eps and per-phase diagnostics."""
    N = len(vecs)
    g = 4 * d
    x = [F(0)] * N
    phases = []
    while True:
        A = [i for i in range(N) if abs(x[i]) < 1]
        if not A:
            break
        Aset = set(A)
        groups = []
        for order in (pi, rho):
            act = [i for i in order if i in Aset]
            for s in range(0, len(act) - g + 1, g):
                groups.append(act[s:s + g])
        rows = []
        for G in groups:
            for c in range(d):
                rows.append({i: vecs[i][c] for i in G})
        neq = len(rows)
        x_old = list(x)
        frozen = set()
        while True:
            cols = [i for i in A if i not in frozen]
            y = nullspace_vector(rows, cols)
            if y is None:
                break
            tmax = None
            hit = None
            for i, yi in y.items():
                if yi == 0:
                    continue
                t = (1 - x[i]) / yi if yi > 0 else (-1 - x[i]) / yi
                if tmax is None or t < tmax:
                    tmax, hit = t, i
            for i, yi in y.items():
                x[i] += tmax * yi
            frozen.add(hit)
            for i in cols:
                if abs(x[i]) == 1:
                    frozen.add(i)
        newA = [i for i in range(N) if abs(x[i]) < 1]
        phases.append((len(A), neq, len(newA), x_old, list(x)))
        if len(newA) == len(A):
            raise RuntimeError("no progress")
    return x, phases


def check_baseline(rng):
    ok = True
    cases = 0
    worst_ratio = F(0)
    max_phases = 0
    max_n = 0
    for _ in range(40):
        d = rng.randint(1, 3)
        N = rng.randint(1, 40)
        pi = list(range(N)); rng.shuffle(pi)
        rho = list(range(N)); rng.shuffle(rho)
        vecs = [rand_ball_vector(rng, d) for _ in range(N)]
        eps, phases = baseline_round(vecs, pi, rho, d)
        cases += 1
        max_n = max(max_n, N)
        if any(abs(e) != 1 for e in eps):
            ok = False
        T = len(phases)
        logbound = N.bit_length()  # floor(log2 N) + 1
        if T > logbound:
            ok = False
        max_phases = max(max_phases, T)
        per = 2 * (4 * d - 1)
        for (a, neq, na, xo, xn) in phases:
            if 2 * neq > a or 2 * na > a:
                ok = False
            for order in (pi, rho):
                so = zero(d)
                sn = zero(d)
                for i in order:
                    so = vadd(so, vscale(xo[i], vecs[i]))
                    sn = vadd(sn, vscale(xn[i], vecs[i]))
                    if sqn(vadd(sn, vscale(-1, so))) > per * per:
                        ok = False
        final = max_sq_two_order(pi, rho, vecs, eps, d)
        bound = (per * T) ** 2
        if final > bound:
            ok = False
        if bound:
            worst_ratio = max(worst_ratio, final / bound)
    report("B_baseline_dlogN_rounding", ok,
           f"cases={cases} max_N={max_n} max_phases={max_phases} "
           f"max_squared_ratio_to_bound={float(worst_ratio):.6f}")


# ---------------------------------------------------------------- Check R
def check_reis(rng):
    """Replay of Reis, Theorem 142 instance values for k=1..4 (unnormalized)."""
    ok = True
    vals = []
    for k in range(1, 5):
        N = 2 * k + 1
        t = k + 1
        w = [F(t + 1) if (i + 1) % 2 == 1 else F(t) for i in range(N)]
        pi = list(range(N))
        rho = []
        for j in range(k, 0, -1):
            rho += [2 * j - 1, 2 * j]   # 0-indexed elements 2j, 2j+1
        rho.append(0)
        best = None
        for eps in all_signings(N):
            m = max(max(abs(s[0]) for s in prefix_sums(pi, [(x,) for x in w], eps, 1)),
                    max(abs(s[0]) for s in prefix_sums(rho, [(x,) for x in w], eps, 1)))
            best = m if best is None else min(best, m)
        normalized = best / (t + 1)
        vals.append(str(normalized))
        if best != 2 * k + 2:
            ok = False
    report("R_reis_theorem142_values", ok,
           "normalized_disc_k1..4=" + ",".join(vals))


# ---------------------------------------------------------------- Check E
def check_explored_instance(rng):
    """Exact value of the N=7 instance found by the exploratory minimax search."""
    k = 3
    N = 2 * k + 1
    pi = list(range(N))
    rho = []
    for j in range(k, 0, -1):
        rho += [2 * j - 1, 2 * j]
    rho.append(0)
    w = [F(1), F(5, 6), F(1), F(5, 6), F(1), F(2, 3), F(1)]
    vecs = [(x,) for x in w]
    best = None
    for eps in all_signings(N):
        m = max_sq_two_order(pi, rho, vecs, eps, 1)
        best = m if best is None else min(best, m)
    report("E_explored_N7_instance_exact_value", best == F(25, 9),
           f"min_max_prefix_squared={best} (value 5/3; below the d=1 lower bound 2 from Reis Thm 142)")


# ---------------------------------------------------------------- controls
def check_controls(rng):
    """Deliberately wrong variants must be detected."""
    detected_A1 = False
    for _ in range(50):
        N = rng.randint(2, 6)
        pi = list(range(N)); rng.shuffle(pi)
        rho = list(range(N)); rng.shuffle(rho)
        a = {pi[k]: k + 1 for k in range(N)}
        b = {rho[k]: k + 1 for k in range(N)}
        vecs = [(F(1),) for _ in range(N)]
        iv = [(F(a[i]), F(2 * N - b[i])) for i in range(N)]   # off by one
        for eps in all_signings(N):
            pr = prefix_sums(rho, vecs, eps, 1)
            for k in range(1, N + 1):
                if coverage(iv, vecs, eps, F(2 * N + 1 - k), 1) != pr[k]:
                    detected_A1 = True
        if detected_A1:
            break
    detected_M = False
    for _ in range(50):
        N = rng.randint(2, 6)
        pi = list(range(N)); rng.shuffle(pi)
        rho = list(range(N)); rng.shuffle(rho)
        w = [F(rng.randint(1, 10), 10) for _ in range(N)]
        tau = [(i, +1) for i in pi] + [(i, +1) for i in rho]   # wrong sign copy
        for delta in all_signings(N):
            B = {(i, delta[i]) for i in range(N)}
            run = F(0); vals = []
            for (i, s) in tau:
                run += w[i] * ((1 if (i, s) in B else 0) - F(1, 2))
                vals.append(run)
            total = sum(w[i] * delta[i] for i in range(N))
            qq = F(0)
            for k in range(N):
                qq += w[rho[k]] * delta[rho[k]]
                if vals[N + k] != total / 2 - qq / 2:
                    detected_M = True
        if detected_M:
            break
    report("C_negative_controls_detected", detected_A1 and detected_M,
           f"offbyone_interval={detected_A1} wrong_copy_sign={detected_M}")


def main():
    rng = random.Random(SEED)
    check_A1(rng)
    check_A2(rng)
    check_A3(rng)
    check_matroid(rng)
    check_baseline(rng)
    check_reis(rng)
    check_explored_instance(rng)
    check_controls(rng)
    print("SUMMARY:", "ALL_PASS" if not FAILS else "FAILURES " + ",".join(FAILS))
    print("SCOPE: finite exact replays only; T2 remains UNRESOLVED")
    return 0 if not FAILS else 1


if __name__ == "__main__":
    sys.exit(main())
