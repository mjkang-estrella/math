#!/usr/bin/env python3
"""Finite checks for the T333E107 r2 contribution review.

These are illustrations of linear algebra and of one explicit local model.
They are NOT a proof of the frozen theorem, of the source contracts, or of
any contribution verdict.  Part A and Part B use exact rational arithmetic;
Part C uses floating point on a finite grid for a model map that is NOT an
exact isometric map from source333.  Standard library only; no file reads.
Writes JSON to stdout.  Run with: python3 -I checks.py > checks.json
"""
from fractions import Fraction as Fr
import json
import math
import random


def dot(a, b):
    return sum(x * y for x, y in zip(a, b))


def sub(a, b):
    return [x - y for x, y in zip(a, b)]


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def scal(c, a):
    return [c * x for x in a]


def det(m):
    """Exact determinant by fraction Gaussian elimination."""
    m = [list(map(Fr, row)) for row in m]
    n = len(m)
    d = Fr(1)
    for i in range(n):
        piv = next((r for r in range(i, n) if m[r][i] != 0), None)
        if piv is None:
            return Fr(0)
        if piv != i:
            m[i], m[piv] = m[piv], m[i]
            d = -d
        d *= m[i][i]
        for r in range(i + 1, n):
            f = m[r][i] / m[i][i]
            for c in range(i, n):
                m[r][c] -= f * m[i][c]
    return d


def nullspace_2x4(r1, r2):
    """Exact basis of {q in Q^4 : <q,r1>=<q,r2>=0}, assuming rank two."""
    rows = [list(map(Fr, r1)), list(map(Fr, r2))]
    # reduced row echelon form
    pivots = []
    r = 0
    for c in range(4):
        piv = next((i for i in range(r, 2) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        pv = rows[r][c]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(2):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        pivots.append(c)
        r += 1
        if r == 2:
            break
    free = [c for c in range(4) if c not in pivots]
    basis = []
    for fc in free:
        q = [Fr(0)] * 4
        q[fc] = Fr(1)
        for i, pc in enumerate(pivots):
            q[pc] = -rows[i][fc]
        basis.append(q)
    return basis


def gamma_x_yy(Fx, Fy, C):
    """Gamma^x_yy = g^{xk}<F_yy,F_k> for the induced metric of (Fx,Fy)."""
    gxx, gxy, gyy = dot(Fx, Fx), dot(Fx, Fy), dot(Fy, Fy)
    dt = gxx * gyy - gxy * gxy
    inv_xx, inv_xy = gyy / dt, -gxy / dt
    return inv_xx * dot(C, Fx) + inv_xy * dot(C, Fy)


def part_a():
    """Exact replay of the author's hostile two-jet, plus full-circle range."""
    Fx = [Fr(1), Fr(0), Fr(0), Fr(0)]
    Fy = [Fr(0), Fr(1), Fr(0), Fr(0)]
    C = [Fr(-1), Fr(0), Fr(2), Fr(0)]
    a2 = Fr(1)
    u = [Fr(2), Fr(0), Fr(1), Fr(0)]
    e4 = [Fr(0), Fr(0), Fr(0), Fr(1)]
    out = {}
    out["gamma_x_yy"] = str(gamma_x_yy(Fx, Fy, C))
    out["P_basis_orthogonal_to_Y_and_C"] = all(
        dot(p, q) == 0 for p in (u, e4) for q in (Fy, C))
    v = scal(dot(Fx, u) / dot(u, u), u)          # e4 component of Fx is 0
    out["v"] = [str(x) for x in v]
    R0sq = dot(v, v) + a2
    out["R0_squared"] = str(R0sq)
    V = scal(Fr(-3, 5), u)
    out["V_on_circle"] = dot(V, V) == R0sq
    w = sub(V, v)
    X = add(Fx, w)
    out["w"] = [str(x) for x in w]
    out["X"] = [str(x) for x in X]
    out["leading_metric_xx_equals_old_plus_a2"] = dot(X, X) == dot(Fx, Fx) + a2
    out["leading_metric_xy_unchanged"] = dot(X, Fy) == dot(Fx, Fy)
    out["orthogonal_tangent_projection_of_X"] = [str(dot(X, Fx)), str(dot(X, Fy))]

    def L(q):
        return [q[0] - 2 * q[2], q[1]]
    out["L_kills_P"] = L(u) == [0, 0] and L(e4) == [0, 0]
    out["L_of_X"] = [str(x) for x in L(X)]
    out["L_of_Fx_Fy"] = [[str(x) for x in L(Fx)], [str(x) for x in L(Fy)]]
    # Projection to span(Y,C)=P^perp: X and Fx have identical components.
    out["spanYC_components_of_X_equal_those_of_Fx"] = (
        dot(X, Fy) == dot(Fx, Fy) and dot(X, C) == dot(Fx, C))
    # Over the whole velocity circle V=R0(cos t u/|u| + sin t e4), the
    # orthogonal tangential x-component of X is 1/5 + (6/5)cos t.
    # Exact at the extreme phases t=0 and t=pi (|u|^2=5, R0^2=9/5):
    # R0*<u/|u|,e1> = R0*2/sqrt5, and (R0*2/sqrt5)^2 = 36/25.
    coeff_sq = R0sq * Fr(4) / dot(u, u)
    out["orth_x_component_range"] = {
        "constant_part": str(1 - v[0]),
        "oscillation_amplitude_squared": str(coeff_sq),
        "min": "1/5 - 6/5 = -1" if coeff_sq == Fr(36, 25) and 1 - v[0] == Fr(1, 5) else "mismatch",
        "max": "1/5 + 6/5 = 7/5" if coeff_sq == Fr(36, 25) else "mismatch",
        "sign_changes_on_circle": True if coeff_sq > (1 - v[0]) ** 2 else False,
    }
    return out


def part_b(seed=333107, samples=4000):
    """Exact equivalence of four formulations of the paid transversality.

    For random integer two-jets with T=span(Fx,Fy) of rank two and Y=Fy,
    C=Fyy independent, test that the following agree:
      (i) Gamma^x_yy != 0;
      (ii) R^4 = T (+) P, i.e. det[Fx,Fy,p1,p2] != 0;
      (iii) orthogonal projection N -> P is an isomorphism (source wording);
      (iv) tangential projections of Y and C are independent (source proof).
    Degenerate samples with Gamma^x_yy = 0 are deliberately included.
    """
    rng = random.Random(seed)
    counts = {"tested": 0, "transverse": 0, "degenerate": 0, "disagreements": 0}
    for k in range(samples):
        Fx = [Fr(rng.randint(-3, 3)) for _ in range(4)]
        Fy = [Fr(rng.randint(-3, 3)) for _ in range(4)]
        if k % 4 == 0:
            # force Gamma^x_yy = 0: C = c*Fy + normal vector
            nb = nullspace_2x4(Fx, Fy) if _rank2(Fx, Fy) else None
            if nb is None:
                continue
            C = add(scal(Fr(rng.randint(-2, 2)), Fy),
                    add(scal(Fr(rng.randint(-2, 2)), nb[0]),
                        scal(Fr(rng.randint(-2, 2)), nb[1])))
        else:
            C = [Fr(rng.randint(-3, 3)) for _ in range(4)]
        if not _rank2(Fx, Fy) or not _rank2(Fy, C):
            continue
        g = gamma_x_yy(Fx, Fy, C)
        Pb = nullspace_2x4(Fy, C)
        Nb = nullspace_2x4(Fx, Fy)
        i = g != 0
        ii = det([Fx, Fy, Pb[0], Pb[1]]) != 0
        # (iii): the map N -> P, n -> orth. projection; with bases this is
        # injective iff the Gram pairing matrix <p_i, n_j> is nonsingular.
        iii = det([[dot(p, n) for n in Nb] for p in Pb]) != 0
        # (iv): tangential parts of Y, C in basis (Fx,Fy) independent:
        # Y_tan=(0,1), C_tan=(Gamma^x,Gamma^y) => independent iff Gamma^x!=0,
        # computed here directly from the Gram system instead.
        gxx, gxy, gyy = dot(Fx, Fx), dot(Fx, Fy), dot(Fy, Fy)
        def tan(q):
            b1, b2 = dot(q, Fx), dot(q, Fy)
            dt = gxx * gyy - gxy * gxy
            return [(gyy * b1 - gxy * b2) / dt, (gxx * b2 - gxy * b1) / dt]
        iv = det([tan(Fy), tan(C)]) != 0
        counts["tested"] += 1
        counts["transverse" if i else "degenerate"] += 1
        if not (i == ii == iii == iv):
            counts["disagreements"] += 1
    return counts


def _rank2(a, b):
    """Exact rank-two test for two vectors in Q^4 via 2x2 minors."""
    for r in range(4):
        for s in range(r + 1, 4):
            if a[r] * b[s] - a[s] * b[r] != 0:
                return True
    return False


def part_c(r=2.0, half=0.25, n=26):
    """Float model: oblique cancellation and orthogonal folding.

    F(x,y)=(x-y^2/2, y, y^2, 0) on [-half,half]^2 (an embedding).  At each
    point P=span(F_y,F_yy)^perp has orthonormal basis (uh, e4).  Model map
    f_z = F + z*W(p,x/z), W = r(sin t uh(p) - cos t e4), so that
    d_x f_z = F_x + r(cos t uh + sin t e4) + O(z).  This is NOT an isometric
    source map; it only exhibits the derivative structure of (5.1).
    """
    def F(x, y):
        return [x - y * y / 2, y, y * y, 0.0]

    def uh(x, y):
        # solve q _|_ F_y=(-y,1,2y,0), F_yy=(-1,0,2,0), e4: q=(2,4y-... )
        # q=(2, 2y*? ...) computed by explicit cross-type formula:
        # q=(a,b,c,0) with -a+2c=0 -> a=2c, and -y a + b + 2y c=0 -> b=0.
        q = [2.0, 0.0, 1.0, 0.0]
        nq = math.sqrt(5.0)
        return [t / nq for t in q]

    def f(z, x, y):
        t = x / z
        u = uh(x, y)
        base = F(x, y)
        return [base[i] + z * r * (math.sin(t) * u[i] - (math.cos(t) if i == 3 else 0.0))
                for i in range(4)]

    res = {"model_amplitude_r": r, "domain_half_width": half, "grid": n}
    for z in (0.02, 0.01):
        pts = [(-half + 2 * half * i / (n - 1), -half + 2 * half * j / (n - 1))
               for i in range(n) for j in range(n)]
        imgs = [f(z, x, y) for x, y in pts]
        worst = float("inf")
        for a in range(len(pts)):
            pa, fa = pts[a], imgs[a]
            for b in range(a + 1, len(pts)):
                pb, fb = pts[b], imgs[b]
                dp = math.hypot(pa[0] - pb[0], pa[1] - pb[1])
                df = math.sqrt(sum((s - t) ** 2 for s, t in zip(fa, fb)))
                worst = min(worst, df / dp)
        # sub-wavelength line test along y=0 (spacing well below z)
        line = [(-half + 2 * half * i / 399, 0.0) for i in range(400)]
        limgs = [f(z, x, y) for x, y in line]
        line_worst = float("inf")
        orth_collision = None
        for a in range(len(line)):
            for b in range(a + 1, len(line)):
                dp = abs(line[a][0] - line[b][0])
                df = math.sqrt(sum((s - t) ** 2 for s, t in zip(limgs[a], limgs[b])))
                line_worst = min(line_worst, df / dp)
                # orthogonal tangent projection (first two coordinates):
                # second coordinate is y=0 on this line, so compare first
                # a<b with first coordinate decreasing by a margin: by the
                # intermediate value theorem the orthogonal tangent projection
                # (which keeps y=0 fixed) is non-injective on this line.
                if orth_collision is None and \
                        limgs[a][0] > limgs[b][0] + 1e-3:
                    orth_collision = [line[a][0], line[b][0],
                                      limgs[a][0] - limgs[b][0]]
        # derivative structure along y=0 by central differences
        h = z * 1e-3
        max_raw_dev = 0.0
        max_oblique_dev = 0.0
        min_orth_x = float("inf")
        for i in range(2001):
            x = -half + 2 * half * i / 2000
            fp, fm = f(z, x + h, 0.0), f(z, x - h, 0.0)
            fx = [(s - t) / (2 * h) for s, t in zip(fp, fm)]
            Fx = [1.0, 0.0, 0.0, 0.0]
            max_raw_dev = max(max_raw_dev, math.sqrt(sum((s - t) ** 2 for s, t in zip(fx, Fx))))
            # oblique projection along P onto T at y=0: L(q)=(q1-2q3, q2)
            Lfx = [fx[0] - 2 * fx[2], fx[1]]
            max_oblique_dev = max(max_oblique_dev, math.hypot(Lfx[0] - 1.0, Lfx[1]))
            min_orth_x = min(min_orth_x, fx[0])
        res["z=%g" % z] = {
            "grid_min_lower_Lipschitz_ratio": worst,
            "line_y0_min_lower_Lipschitz_ratio_sub_wavelength": line_worst,
            "orthogonal_projection_near_collision_on_y0": orth_collision,
            "max_|d_x f_z - F_x|_on_y0": max_raw_dev,
            "max_|L d_x f_z - F_x|_on_y0": max_oblique_dev,
            "min_orthogonal_tangential_x_derivative_on_y0": min_orth_x,
        }
    res["interpretation"] = (
        "Finite grid evidence only. The raw derivative deviation stays order one; "
        "the oblique-projected deviation is O(z) (here exactly 0 up to rounding on y=0 "
        "because uh is constant); a negative orthogonal tangential x-derivative means "
        "the orthogonal tangent projection of f_z folds along y=0.")
    return res


if __name__ == "__main__":
    report = {
        "purpose": "finite illustrations for T333E107 contribution review r2; not proof",
        "part_a_exact_hostile_two_jet": part_a(),
        "part_b_exact_transversality_equivalences": part_b(),
        "part_c_float_local_model": part_c(),
    }
    print(json.dumps(report, indent=1, sort_keys=True))
