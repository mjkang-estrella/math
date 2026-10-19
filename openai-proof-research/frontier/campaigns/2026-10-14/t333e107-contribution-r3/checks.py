#!/usr/bin/env python3
"""Finite illustrative checks for the T333E107 contribution review (round r3).

These are finite computations. They prove nothing about the general theorem,
its correctness, or its novelty. Exact parts use rational arithmetic; the toy
part uses floating point and is a mechanism illustration only.

The program reads nothing and writes nothing; it prints one JSON object.
"""
from fractions import Fraction as Q
import json
import math
import random


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def scale(c, a):
    return [c * x for x in a]


def rank(rows):
    m = [list(r) for r in rows]
    r = 0
    ncols = len(m[0]) if m else 0
    for c in range(ncols):
        piv = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c] / m[r][c]
                m[i] = [x - f * y for x, y in zip(m[i], m[r])]
        r += 1
    return r


def nullspace(rows, n):
    """Exact basis of {q : rows q = 0} in Q^n."""
    m = [list(r) for r in rows]
    pivcols = []
    r = 0
    for c in range(n):
        piv = next((i for i in range(r, len(m)) if m[i][c] != 0), None)
        if piv is None:
            continue
        m[r], m[piv] = m[piv], m[r]
        m[r] = [x / m[r][c] for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [x - f * y for x, y in zip(m[i], m[r])]
        pivcols.append(c)
        r += 1
    free = [c for c in range(n) if c not in pivcols]
    basis = []
    for fc in free:
        v = [Q(0)] * n
        v[fc] = Q(1)
        for i, pc in enumerate(pivcols):
            v[pc] = -m[i][fc]
        basis.append(v)
    return basis


def hostile_two_jet():
    """Author's hostile example F(x,y)=(x-y^2/2, y, y^2, 0) at the origin."""
    e = [[Q(int(i == j)) for j in range(4)] for i in range(4)]
    Fx, Fy, Fyy = e[0], e[1], [Q(-1), Q(0), Q(2), Q(0)]
    g = [[dot(Fx, Fx), dot(Fx, Fy)], [dot(Fy, Fx), dot(Fy, Fy)]]
    assert g == [[1, 0], [0, 1]]
    # Gamma^k_yy = g^{kl} <F_yy, F_l>; here g is the identity.
    gamma_x_yy = dot(Fyy, Fx)
    hess_x_yy = -gamma_x_yy
    P = nullspace([Fy, Fyy], 4)
    assert len(P) == 2
    # orthogonal projection of F_x to P (Gram inverse on the exact basis)
    G = [[dot(P[i], P[j]) for j in range(2)] for i in range(2)]
    det = G[0][0] * G[1][1] - G[0][1] * G[1][0]
    Gi = [[G[1][1] / det, -G[0][1] / det], [-G[1][0] / det, G[0][0] / det]]
    b = [dot(P[i], Fx) for i in range(2)]
    c = [Gi[0][0] * b[0] + Gi[0][1] * b[1], Gi[1][0] * b[0] + Gi[1][1] * b[1]]
    v = add(scale(c[0], P[0]), scale(c[1], P[1]))
    a = Q(1)
    R0sq = dot(v, v) + a * a
    u = [Q(2), Q(0), Q(1), Q(0)]  # in P, |u|^2 = 5
    V = scale(Q(-3, 5), u)
    w = add(V, scale(-1, v))
    X = add(Fx, w)
    # orthogonal projection to the old tangent plane span(e1,e2)
    orth_tangent_X = [X[0], X[1]]

    def L(q):  # oblique base projection killing P, identity on dF(T)
        return [q[0] - 2 * q[2], q[1]]

    # a second admissible phase on the same circle
    V2 = scale(Q(3, 5), u)
    X2 = add(Fx, add(V2, scale(-1, v)))
    t = Q(7, 12)
    Xavg = add(scale(t, X), scale(1 - t, X2))
    out = {
        "metric_identity_at_origin": g == [[1, 0], [0, 1]],
        "Gamma_x_yy": str(gamma_x_yy),
        "Hess_x_yy": str(hess_x_yy),
        "P_contains_(2,0,1,0)_and_e4": rank(P + [u]) == 2 and rank(P + [e[3]]) == 2,
        "v": [str(x) for x in v],
        "R0_squared": str(R0sq),
        "V_on_circle": dot(V, V) == R0sq and dot(V2, V2) == R0sq,
        "V_in_P": dot(V, Fy) == 0 and dot(V, Fyy) == 0,
        "w": [str(x) for x in w],
        "X": [str(x) for x in X],
        "leading_metric_xx_equals_|Fx|^2+a^2": dot(X, X) == dot(Fx, Fx) + a * a,
        "leading_metric_xy_unchanged": dot(X, Fy) == dot(Fx, Fy),
        "orthogonal_tangent_projection_of_X": [str(x) for x in orth_tangent_X],
        "L_kills_P": all(L(p) == [0, 0] for p in P),
        "L_of_Fx_Fy": [[str(x) for x in L(Fx)], [str(x) for x in L(Fy)]],
        "L_of_X": [str(x) for x in L(X)],
        "convex_combination_weight": str(t),
        "orthogonal_tangent_projection_of_convex_combination":
            [str(Xavg[0]), str(Xavg[1])],
        "L_of_convex_combination": [str(x) for x in L(Xavg)],
        # pointwise metric dominance |X(theta)|>=|F_x| holds at both phases,
        # but fails for their convex combination
        "norm_sq_X_at_two_phases": [str(dot(X, X)), str(dot(X2, X2))],
        "norm_sq_Fx": str(dot(Fx, Fx)),
        "norm_sq_convex_combination": str(dot(Xavg, Xavg)),
    }
    assert dot(X, X) >= dot(Fx, Fx) and dot(X2, X2) >= dot(Fx, Fx)
    assert dot(Xavg, Xavg) == Q(1, 4) < dot(Fx, Fx)
    assert out["Gamma_x_yy"] == "-1" and out["R0_squared"] == "9/5"
    assert out["w"] == ["-2", "0", "-1", "0"] and out["X"] == ["-1", "0", "-1", "0"]
    assert orth_tangent_X == [-1, 0] and L(X) == [1, 0]
    assert Xavg[0] == 0 and Xavg[1] == 0 and L(Xavg) == [1, 0]
    return out


def duality_trials(n_trials=400, seed=20261018):
    """P=span(Y,C)^perp meets T=span(Fx,Fy) trivially  <=>  span(Y,C) meets
    N=T^perp trivially  <=>  tangential projections of Y,C are independent.
    Random rational instances, including deliberately degenerate ones."""
    rng = random.Random(seed)
    counts = {"trials": 0, "transverse": 0, "degenerate": 0, "agreements": 0}
    for k in range(n_trials):
        def rv():
            return [Q(rng.randint(-4, 4), rng.randint(1, 3)) for _ in range(4)]
        Fx, Fy = rv(), rv()
        if rank([Fx, Fy]) < 2:
            continue
        Y = Fy
        C = rv()
        if k % 4 == 0:  # force a normal vector into span(Y,C)
            nb = nullspace([Fx, Fy], 4)
            C = add(scale(Q(rng.randint(-2, 2)), Y), nb[0])
        if rank([Y, C]) < 2:
            continue
        P = nullspace([Y, C], 4)
        N = nullspace([Fx, Fy], 4)
        a1 = rank([Fx, Fy] + P) == 4          # T + P = R^4
        a2 = rank([Y, C] + N) == 4            # span(Y,C) + N = R^4
        # tangential components as coordinates in the (Fx,Fy) Gram basis
        Gm = [[dot(Fx, Fx), dot(Fx, Fy)], [dot(Fy, Fx), dot(Fy, Fy)]]
        tY = [dot(Y, Fx), dot(Y, Fy)]
        tC = [dot(C, Fx), dot(C, Fy)]
        a3 = rank([tY, tC]) == 2
        counts["trials"] += 1
        counts["transverse" if a1 else "degenerate"] += 1
        if a1 == a2 == a3:
            counts["agreements"] += 1
        assert Gm[0][0] * Gm[1][1] - Gm[0][1] ** 2 != 0
    assert counts["agreements"] == counts["trials"] and counts["degenerate"] > 0
    return counts


def toy_mechanism(z_values=(0.02, 0.01, 0.005), n=25, amp=3.0):
    """Floating toy: F(x,y)=(x-y^2/2, y, y^2, 0) on [-0.3,0.3]^2 and
    f=F+z*Wprim(p, x/z), with the oscillation w(p,theta)=amp*(cos t u1+sin t u2)
    in the pointwise plane P(p)=span(F_y,F_yy)^perp. Not the source loop and not
    an isometric map; it isolates only the projection mechanism."""
    def F(x, y):
        return [x - y * y / 2, y, y * y, 0.0]

    def frame(y):
        # q.F_yy=0 gives q1=2q3; then q.F_y=-2y q3+q2+2y q3=q2=0. Hence
        # P(x,y)=span((2,0,1,0),e4) for every point of this toy chart.
        u1 = [c / math.sqrt(5.0) for c in (2.0, 0.0, 1.0, 0.0)]
        u2 = [0.0, 0.0, 0.0, 1.0]
        return u1, u2

    def f(x, y, z):
        u1, u2 = frame(y)
        th = x / z
        # mean-zero primitive of amp*(cos th u1 + sin th u2) in theta
        Wv = [amp * (math.sin(th) * a - math.cos(th) * b) for a, b in zip(u1, u2)]
        return add(F(x, y), [z * c for c in Wv])

    def L(q):
        return [q[0] - 2 * q[2], q[1]]

    pts = [(-0.3 + 0.6 * i / (n - 1), -0.3 + 0.6 * j / (n - 1))
           for i in range(n) for j in range(n)]
    res = []
    h = 1e-7
    for z in z_values:
        worst_L = 0.0
        worst_orth = 0.0
        for (x, y) in pts:
            fx = [(a - b) / (2 * h) for a, b in zip(f(x + h, y, z), f(x - h, y, z))]
            fy = [(a - b) / (2 * h) for a, b in zip(f(x, y + h, z), f(x, y - h, z))]
            Fx = [1.0, 0.0, 0.0, 0.0]
            Fy = [-y, 1.0, 2 * y, 0.0]
            dL = [a - b for a, b in zip(L(fx) + L(fy), L(Fx) + L(Fy))]
            worst_L = max(worst_L, max(abs(c) for c in dL))
            # orthogonal projection onto the old tangent plane at the same point
            G = [[dot(Fx, Fx), dot(Fx, Fy)], [dot(Fy, Fx), dot(Fy, Fy)]]
            det = G[0][0] * G[1][1] - G[0][1] ** 2

            def coords(q):
                b0, b1 = dot(q, Fx), dot(q, Fy)
                return [(G[1][1] * b0 - G[0][1] * b1) / det,
                        (-G[1][0] * b0 + G[0][0] * b1) / det]
            d0 = [a - b for a, b in zip(coords(fx) + coords(fy), [1.0, 0.0, 0.0, 1.0])]
            worst_orth = max(worst_orth, max(abs(c) for c in d0))
        rng = random.Random(7)
        min_ratio = float("inf")
        for _ in range(20000):
            p = rng.choice(pts)
            if rng.random() < 0.5:
                q = (p[0] + rng.uniform(-0.05, 0.05), p[1] + rng.uniform(-0.05, 0.05))
            else:
                q = rng.choice(pts)
            d = math.hypot(p[0] - q[0], p[1] - q[1])
            if d < 1e-9:
                continue
            fp, fq = f(p[0], p[1], z), f(q[0], q[1], z)
            min_ratio = min(min_ratio, math.dist(fp, fq) / d)
        res.append({"z": z,
                    "sup_grid_|D(L f)-D(L F)|": round(worst_L, 6),
                    "sup_grid_|orthogonal_tangent_coords(df)-id|": round(worst_orth, 6),
                    "min_sampled_chord_ratio": round(min_ratio, 6)})
    return res


def main():
    out = {
        "status": "FINITE_ILLUSTRATIONS_NOT_PROOF",
        "hostile_two_jet_exact": hostile_two_jet(),
        "complement_duality_exact_random_trials": duality_trials(),
        "toy_projection_mechanism_float": toy_mechanism(),
        "certifies_theorem_or_contribution": False,
    }
    print(json.dumps(out, indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
