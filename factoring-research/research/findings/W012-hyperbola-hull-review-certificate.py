"""W012 hyperbola-hull review: exact fixed-instance certificates.

Not a candidate algorithm, performance run, or sweep. Two fixed semiprimes,
fixed moduli and five fixed query points chosen before execution check the
algebra and inequalities derived in W012-hyperbola-hull-review.md.
Python standard library only; run with `python3 -I <this file> <output.json>`.
"""

import json
import sys
from fractions import Fraction
from math import gcd, isqrt
from decimal import Decimal, getcontext

getcontext().prec = 80

INSTANCES = [(101, 103), (1009, 1013)]          # fixed, declared in advance
LATTICE_CASES = [((101, 103), 5), ((1009, 1013), 11)]
CARD_B_H = {1022117: [511, 766, 894, 958, 990]}  # fixed midpoints-ish of [2, isqrt N]

checks = []


def check(name, ok, **data):
    checks.append({"name": name, "passed": bool(ok), **data})


def ceil_div(a, b):
    return -((-a) // b)


def lower_hull(points):
    """Lower convex chain of points sorted by x (monotone chain)."""
    hull = []
    for p in points:
        while len(hull) >= 2:
            (x1, y1), (x2, y2) = hull[-2], hull[-1]
            # remove hull[-1] if it is not strictly below segment hull[-2] -> p
            if (x2 - x1) * (p[1] - y1) - (y2 - y1) * (p[0] - x1) <= 0:
                hull.pop()
            else:
                break
        hull.append(p)
    while len(hull) >= 2 and hull[-1][1] >= hull[-2][1]:
        hull.pop()  # horizontal tail belongs to the unbounded ray, not to new vertices
    return hull


def cones(hull):
    """Closed normal cone [lo, hi] of lambda for objective lambda*x + y."""
    out = []
    for k, (x, y) in enumerate(hull):
        hi = None if k == 0 else Fraction(hull[k - 1][1] - y, x - hull[k - 1][0])
        lo = Fraction(0) if k == len(hull) - 1 else Fraction(y - hull[k + 1][1], hull[k + 1][0] - x)
        out.append((lo, hi))
    return out


def dsqrt(fr):
    return (Decimal(fr.numerator) / Decimal(fr.denominator)).sqrt()


def p_range(N, lo, hi):
    """Real interval of tangent abscissae sqrt(N/lambda), lambda in [lo, hi]."""
    left = Decimal(0) if hi is None else dsqrt(Fraction(N) / hi)
    right = Decimal("Infinity") if lo == 0 else dsqrt(Fraction(N) / lo)
    return left, right


def standard_hull_checks(P, Q):
    N = P * Q
    pts = [(x, ceil_div(N, x)) for x in range(1, N + 1)]
    hull = lower_hull(pts)
    cs = cones(hull)
    verts = {v: c for v, c in zip(hull, cs)}
    # (1) factor points are vertices; tangent slope strictly inside own cone
    for f in [(1, N), (P, Q), (Q, P), (N, 1)]:
        lam = Fraction(N, f[0] ** 2)
        lo, hi = verts.get(f, (None, None))
        inside = f in verts and lo < lam and (hi is None or lam < hi)
        check(f"N={N}: factor {f} is vertex with N/P^2 strictly inside its normal cone",
              inside, cone=[str(lo), str(hi)])
    # (2) no factor slope lies in a closed cone of a non-factor vertex
    bad = 0
    for v, (lo, hi) in verts.items():
        if v[0] * v[1] == N:
            continue
        for p in (1, P, Q, N):
            lam = Fraction(N, p * p)
            if lo <= lam and (hi is None or lam <= hi):
                bad += 1
    check(f"N={N}: closed cones of non-factor vertices contain no factor slope", bad == 0)
    # (3) edge ties: edges with interior lattice points exist and those points are not factors
    tie_edges, tie_factor = 0, 0
    for (x1, y1), (x2, y2) in zip(hull, hull[1:]):
        g = gcd(x2 - x1, y1 - y2)
        if g > 1:
            tie_edges += 1
            dx, dy = (x2 - x1) // g, (y1 - y2) // g
            for t in range(1, g):
                if (x1 + t * dx) * (y1 - t * dy) == N:
                    tie_factor += 1
    check(f"N={N}: lattice points interior to hull edges are never factors",
          tie_factor == 0, edges_with_interior_lattice_points=tie_edges)
    # (4) per-vertex P-range width lemma on [N^(1/3), sqrt N]
    A = Decimal(N) ** (Decimal(1) / 3)
    B = Decimal(N).sqrt()
    worst = Decimal(0)
    viol = 0
    for v, (lo, hi) in verts.items():
        left, right = p_range(N, lo, hi)
        a, b = max(left, A), min(right, B)
        if a > b:
            continue
        vx = Decimal(v[0])
        for Pt in (a, b):  # inequality is checked at both ends of the clipped range
            xs = Decimal(max(1, int((Pt + Decimal("0.5")).to_integral_value(rounding="ROUND_FLOOR"))))
            eta = Decimal(N) / (4 * Pt * Pt * xs)
            lhs = (vx - Pt) ** 2
            rhs = (1 + eta) * vx * Pt * Pt / Decimal(N)
            if not lhs < rhs:
                viol += 1
            worst = max(worst, lhs / rhs)
    check(f"N={N}: (v_x-P)^2 < (1+eta) v_x P^2/N at clipped cone ends in [N^(1/3), sqrt N]",
          viol == 0, max_ratio=str(round(worst, 6)))
    # (5) central block count between rigorous lower and Andrews-Rabinowitz upper bound
    Ac, Bc = B / 2, B
    central = [v for v, (lo, hi) in verts.items()
               if max(p_range(N, lo, hi)[0], Ac) <= min(p_range(N, lo, hi)[1], Bc)]
    eta_c = 2 / (B - 1)
    r = ((1 + eta_c) * (Bc + ((1 + eta_c) * Bc).sqrt() + 1 + eta_c)).sqrt()
    lower = (Bc - Ac) / (2 * r)
    x_in = [v for v in hull if Ac <= v[0] <= Bc]
    kappa2 = 2 * float(Decimal(3.141592653589793) ** (Decimal(2) / 3))
    upper = kappa2 * (float(N) / 4 * (1 + 2 / float(B))) ** (1 / 3) + 2
    check(f"N={N}: cone-ranges meeting [sqrtN/2, sqrtN] >= (sqrtN/2)/(2r)",
          len(central) >= lower, count=len(central), lower=str(round(lower, 3)))
    check(f"N={N}: vertices with x in [sqrtN/2, sqrtN] <= 2pi^(2/3)(area/2)^(1/3)+2",
          len(x_in) <= upper, count=len(x_in), upper=round(upper, 3))
    # (6) full-hull counts against Corollary 1.2 lower bound and lower-bound location
    lb = 2 * N ** (1 / 3) - 2
    check(f"N={N}: full hull has >= 2N^(1/3)-2 vertices (Cor. 1.2)", len(hull) >= lb,
          count=len(hull), lower=round(lb, 3))
    first_lines = int(round(N ** (1 / 3)))
    while first_lines ** 3 > N:
        first_lines -= 1
    cols = {v[0] for v in hull}
    check(f"N={N}: each column x=1..floor(N^(1/3)) holds a vertex (Prop. 2.9 lines)",
          all(x in cols for x in range(1, first_lines + 1)), lines=first_lines)
    return {"N": N, "vertices": len(hull), "central_cone_count": len(central),
            "central_x_count": len(x_in)}


def residue_lattice_checks(P, Q, m):
    N = P * Q
    j = P % m
    assert gcd(N, m) == 1
    r = N * pow(j * j, -1, m) % m
    (u1, t1), (u2, t2) = (m, 0), (r, 1)
    check(f"N={N},m={m}: oriented basis of Lambda_j has u1*t2-u2*t1=m", u1 * t2 - u2 * t1 == m)
    m2 = m * m
    jinv = pow(j, -1, m2)
    v = []
    for (u, t) in ((u1, t1), (u2, t2)):
        vi = (-(u * j * j + N * t) * jinv) % m2
        v.append(vi)
        check(f"N={N},m={m}: row ({u},{t}) congruences (1)",
              (u * j * j + vi * j + N * t) % m2 == 0 and (vi + 2 * u * j) % m == 0)
    v1, v2 = v
    i1 = Fraction(u1 * P + v1 + t1 * Q, m2)
    i2 = Fraction(u2 * P + v2 + t2 * Q, m2)
    check(f"N={N},m={m}: true factor gives integer quotients (2)",
          i1.denominator == 1 and i2.denominator == 1)
    alpha = Fraction(-(t2 * v1 - t1 * v2), m)
    beta = Fraction(u2 * v1 - u1 * v2, m)
    Pr = m * (t2 * i1 - t1 * i2) + alpha
    Qr = m * (-u2 * i1 + u1 * i2) + beta
    check(f"N={N},m={m}: inverse map (3) recovers (P,Q), constants integral",
          (Pr, Qr) == (P, Q) and alpha.denominator == 1 and beta.denominator == 1)
    # quadratic part of P*Q in (i1,i2): m^2 * (t2 i1 - t1 i2)(-u2 i1 + u1 i2)
    a = m2 * t2 * (-u2)
    b = m2 * (t2 * u1 + t1 * u2)
    c = m2 * (-t1) * u1
    disc = b * b - 4 * a * c
    content = gcd(gcd(a, b), c)
    ap, bp, cp = a // content, b // content, c // content
    dp = bp * bp - 4 * ap * cp
    check(f"N={N},m={m}: sqrt discriminant = m^3; content = m^2; primitive sqrt disc = m",
          disc == m ** 6 and content == m2 and dp == m * m,
          a=a, b=b, c=c, content=content)
    # paper normalisation: n = N/m^2, Delta = m, n/Delta = N/m^3; Thm 1.1 bounds
    nD = Fraction(N, m ** 3)
    M_prim = max(2 * m, nD)
    M_raw = max(2 * m ** 3, nD)
    # residue lattice in (P,Q): vertical lines P = j mod m, Q-step m^2 on each line
    q_res = [q for q in range(1, 3 * m2 + 1) if (P * q - N) % m2 == 0 and q % m == (N * pow(j, -1, m)) % m]
    steps = {q2 - q1 for q1, q2 in zip(q_res, q_res[1:])}
    check(f"N={N},m={m}: on line P={P}, L_j has Q-step m^2", steps == {m2})
    # reduced coordinates (a,b) with j*b + (N/j)*a = 0 mod m: projections onto both axes are Z
    Q0 = N * pow(j, -1, m) % m
    proj_a = {aa % m for aa in range(m) for bb in range(m) if (j * bb + Q0 * aa) % m == 0}
    proj_b = {bb % m for aa in range(m) for bb in range(m) if (j * bb + Q0 * aa) % m == 0}
    check(f"N={N},m={m}: rescaled linear lattice is reduced (Def. 3.1), index m",
          proj_a == set(range(m)) and proj_b == set(range(m)) and len(proj_a) == m)
    # hull of L_j intersect H in (P,Q): lowest admissible Q on each admissible column
    pts = []
    Pcol = j if j > 0 else m
    while Pcol <= N + m2 * m:
        if gcd(Pcol, m) == 1:
            qs = N * pow(Pcol, -1, m2) % m2
            target = max(ceil_div(N, Pcol), 1)
            qq = target + ((qs - target) % m2)
            pts.append((Pcol, qq))
        Pcol += m
    hull = lower_hull(pts)
    cs = cones(hull)
    verts = dict(zip(hull, cs))
    lam = Fraction(N, P * P)
    lo, hi = verts.get((P, Q), (None, None))
    check(f"N={N},m={m}: factor (P,Q) is vertex of conv(H cap L_j), slope strictly inside",
          (P, Q) in verts and lo < lam and (hi is None or lam < hi))
    full_lb = 2 * float(nD) ** (1 / 3) - 2
    check(f"N={N},m={m}: residue hull count >= 2(N/m^3)^(1/3)-2 (Thm 1.1, Delta=m)",
          len(hull) >= full_lb, count=len(hull), lower=round(full_lb, 3))
    # residue width lemma: (v_x-P)^2 < m^2 (1+eta') v_x P^2/N on [N^(1/3), sqrt N]
    A = Decimal(N) ** (Decimal(1) / 3)
    B = Decimal(N).sqrt()
    viol, worst = 0, Decimal(0)
    for vtx, (clo, chi) in verts.items():
        left, right = p_range(N, clo, chi)
        aa, bb = max(left, A), min(right, B)
        if aa > bb:
            continue
        vx = Decimal(vtx[0])
        for Pt in (aa, bb):
            Pp = Pt - m / Decimal(2)  # nearest admissible column is >= P - m/2
            eta = Decimal(N) / (4 * Pt * Pt * Pp)
            lhs = (vx - Pt) ** 2
            rhs = m * m * (1 + eta) * vx * Pt * Pt / Decimal(N)
            if not lhs < rhs:
                viol += 1
            worst = max(worst, lhs / rhs)
    check(f"N={N},m={m}: residue width lemma at clipped cone ends", viol == 0,
          max_ratio=str(round(worst, 6)))
    return {"N": N, "m": m, "j": j, "basis": [[u1, t1], [u2, t2]], "v": v,
            "form": [a, b, c], "n_over_Delta": str(nD), "M_primitive": str(M_prim),
            "M_raw_unnormalised": str(M_raw), "residue_hull_vertices": len(hull)}


def card_b_gap_checks(N, hs):
    R = isqrt(N)
    out = []
    for h in hs:
        g = gcd(N, h * h)
        a, b = N // g, h * h // g
        s = min(a * x + b * ceil_div(N, x) for x in range(2, R + 1))
        excl = [x for x in range(2, R + 1) if a * x * x - s * x + b * N < 0]
        X = max(excl) if excl else 0
        bound = 3 + 2 * (X ** 1.5) / N ** 0.5
        contiguous = excl == list(range(excl[0], excl[-1] + 1)) if excl else True
        check(f"N={N}, h={h}: Card B exclusion is an integer interval of size <= 3+2X^(3/2)/sqrtN",
              contiguous and len(excl) <= bound and (h in excl), size=len(excl),
              bound=round(bound, 3))
        out.append({"h": h, "excluded": len(excl), "bound": round(bound, 3)})
    return out


def main(path):
    std = [standard_hull_checks(P, Q) for P, Q in INSTANCES]
    lat = [residue_lattice_checks(P, Q, m) for (P, Q), m in LATTICE_CASES]
    cb = {N: card_b_gap_checks(N, hs) for N, hs in CARD_B_H.items()}
    # symbolic identity: (al*de + be*ga)^2 - 4*al*be*ga*de == (al*de - be*ga)^2 (polynomial identity;
    # checked on a fixed grid only as a typo guard, the identity itself is expanded in the report)
    ok = all((al * de + be * ga) ** 2 - 4 * al * be * ga * de == (al * de - be * ga) ** 2
             for al in range(-3, 4) for be in range(-3, 4) for ga in range(-3, 4) for de in range(-3, 4))
    check("product-of-linear-forms discriminant identity (typo guard)", ok)
    result = {"checks": checks, "all_passed": all(c["passed"] for c in checks),
              "count": len(checks), "standard": std, "residue": lat, "card_b": cb}
    with open(path, "w") as fh:
        json.dump(result, fh, indent=1, default=str)
    print(json.dumps({"all_passed": result["all_passed"], "count": len(checks)}))


if __name__ == "__main__":
    main(sys.argv[1])
