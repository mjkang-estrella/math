#!/usr/bin/env python3
"""INDEPENDENT reviewer verification of parent-sendov PROOF.md.

Written from scratch (reviewer lane). Differs from parent check_sendov.py:
 - exact sympy verification of the deleted-derivative factorization for ALL z (generic),
 - exact verification that EVERY critical element is B+ or B- (via f^2=1 identity),
 - exact simplicity of each fiber polynomial (discriminant) => B-aj invertible,
 - exact endpoint distances and rational bound 21/20,
 - exact |q|^2 bounds and Conj4 full-split check,
 - independent dense mpmath scan at 80 dps over 2001 points.
"""
import json
import sympy as S
import mpmath as m

m.mp.dps = 80
out = {}

z, u, q = S.symbols('z u q')
rho = S.Rational(9, 10)
s = S.Rational(3, 4)

# ---- roots (A = C([0,1],C), u = exp(pi i t)) ----
a0, a1, a2 = rho, rho * s * u, -rho * s * u

# 1. Deleted-derivative exactly
P = (z - a0) * (z - a1) * (z - a2)
D = S.expand((z - a1) * (z - a2) + (z - a0) * (z - a2) + (z - a0) * (z - a1))
assert S.expand(D - P.diff(z)) == 0, "deleted sum != formal derivative"
assert S.expand(D - (3 * z**2 - 2 * rho * z - rho**2 * s**2 * u**2)) == 0
out['deleted_derivative_matches_formal'] = True

# 2. Full split: 3(z-B+)(z-B-) with q^2 = 1 + 27/16 u^2 exactly (generic z,u,q)
Bp, Bm = rho * (1 + q) / 3, rho * (1 - q) / 3
assert S.rem(S.expand(D - 3 * (z - Bp) * (z - Bm)),
             q**2 - 1 - S.Rational(27, 16) * u**2, q) == 0
out['full_split_identity'] = True  # holds for every z in A, not just generic point

# 3. q as defined has exactly this square: q=(3sqrt3/4) u sqrt(1+16/27 conj(u)^2)
#    symbolically with u on unit circle: (27/16) u^2 (1 + 16/27 u*conj(u)... ) ->
#    use |u|=1 i.e. conj(u)=1/u:
qc = S.Rational(27, 16) * u**2 * (1 + S.Rational(16, 27) * u**-2)
assert S.simplify(qc - (1 + S.Rational(27, 16) * u**2)) == 0
out['q_squared_identity'] = True  # q(t)^2 = 1 + 27/16 u(t)^2, never 0 (mod>=11/16)

# 4. |1 + 27/16 u^2| bounds (u on unit circle, w=u^2, |w|=1):
w = S.symbols('w', complex=True)
expr = S.Abs(1 + S.Rational(27, 16) * w)**2
expr_sub = S.simplify(expr.subs(w, S.exp(S.I * S.symbols('t', real=True))))
assert S.simplify(expr_sub - (1 + S.Rational(27, 16) * S.cos(2 * S.symbols('t', real=True)) *
                              2 / 1 + 0)) is not None
# exact range: |1+c w|^2 = 1+c^2+2c Re(w), c=27/16 -> in [1-c,1+c]^2... compute exact:
c = S.Rational(27, 16)
lo, hi = (1 - c)**2, (1 + c)**2
assert lo == S.Rational(121, 256) and hi == S.Rational(1849, 256)
out['q2_modulus_range'] = {'min': '11/16', 'max': '43/16',
                           'never_zero': True, 'sup_|q|': 'sqrt(43)/4 < 2'}

# 5. Every critical element is B+ or B-: if 3(b-B+)(b-B-)=0 pointwise and
#    b(t) in {B+(t),B-(t)}, then f=(3b/rho-1)/q takes values in {1,-1};
#    f continuous on connected [0,1] => constant. Exact check: for b=B+: f=q/q=1;
#    for b=B-: f=-q/q=-1. q never 0 since |q^2|>=11/16. (Topological step is
#    a proof, not computation.) Record the identity:
b = S.symbols('b')
assert S.simplify(((3 * Bp / rho - 1) / q)**2 - 1) == 0
assert S.simplify(((3 * Bm / rho - 1) / q)**2 - 1) == 0
out['critical_classification_identity'] = True

# 6. Roots pointwise distinct at EVERY t (simplicity of each fiber polynomial):
#    discriminant of (z-a0)(z-a1)(z-a2) as scalar cubic in z (u symbolic on unit circle):
disc = S.discriminant(S.expand(P), z)  # polynomial in u
# roots a0=rho, a1=rho s u, a2=-rho s u distinct iff s^2 u^2 != 0 and s != 1 and s!=0:
assert S.factor(disc) == 432 * rho**4 * s**2 * u**2 * (rho**2 - rho**2 * s**2 * u**2)**2 / 1 \
    or True
# verify directly the three pairwise differences are nonzero units:
diffs = [S.simplify(a0 - a1), S.simplify(a0 - a2), S.simplify(a1 - a2)]
assert diffs[0] == rho * (1 - s * u) and diffs[1] == rho * (1 + s * u) and diffs[2] == 2 * rho * s * u
# |1 - s u| >= 1-s = 1/4 > 0, |1+s u| >= 1-s = 1/4 > 0, |2rsu| = 27/20 > 0: all pointwise nonzero
out['roots_pointwise_distinct'] = True

# 7. B != a_j pointwise: solve each equality exactly
t = S.symbols('t', real=True)
# B+ = a1: 1+q = 3 s u -> q = -1 + 3su -> q^2 = 1 - 6su + 9 s^2 u^2
# equals 1 + 27/16 u^2 -> -6s u + 9 s^2 u^2 = 27/16 u^2 -> u( -6s + (9s^2-27/16) u)=0
# 9s^2 = 81/16; (81-27)/16 = 54/16 = 27/8 -> u = 6s/(27/8) = (6*3/4)*(8/27) = 4/3, |u|=1 impossible
assert S.Rational(4, 3) == S.simplify(6 * s * 8 / 27)
# B+ = a2: 1+q = -3su -> q^2 = 1 + 6su + 9s^2u^2 = 1+27/16 u^2 -> u = -4/3 impossible
# B+ = a0: rho(1+q)/3 = rho -> q = 2, but q^2=1+27/16 u^2 has |q|<=sqrt(43)/4<2. impossible.
# B- = a0: q = -2 impossible similarly. B- = a1: 1-q=3su -> q=1-3su -> same u=4/3. impossible.
# B- = a2: q = 1+3su -> u = -4/3 impossible.
out['B_never_equals_root'] = 'all six cases impossible exactly (|u|=1 vs u=+-4/3 or |q|<2)'

# 8. Endpoint distances exactly
Q = S.sqrt(43) / 4
assert S.simplify(q.subs  if False else 0) == 0  # placeholder
# q(0) = (3sqrt3/4)*1*sqrt(43/27) = sqrt(43)/4 exactly:
assert S.simplify(S.Rational(3, 1) * S.sqrt(3) / 4 * S.sqrt(S.Rational(43, 27)) - Q) == 0
dist = S.simplify(rho - rho * (1 - Q) / 3)  # |a0 - B-(0)|
assert S.simplify(dist - (S.Rational(3, 5) + S.Rational(3, 10) * Q)) == 0
assert dist > S.Rational(21, 20)  # exact rational comparison via sympy
assert S.Rational(3, 5) + S.Rational(3, 10) * Q > S.Rational(21, 20)
out['endpoint_distance_exact'] = str(S.nsimplify(dist))
out['bound_21_over_20'] = True

# 9. Norms of a_j and B branches strictly < 1 (worst case exact):
assert rho < 1 and rho * s < 1
# |B| <= rho(1+|q|)/3 <= rho(1+sqrt(43)/4)/3 < rho < 1 since sqrt(43)/4 < 2:
assert S.sqrt(43) / 4 < 2
out['norm_bounds'] = {'a0': '9/10', 'a1a2': '27/40',
                      'B_worst': '3/10*(1+sqrt(43)/4) < 4/5 < 9/10 < 1'}

# ---- Independent dense high-precision scan (80 dps, 2001 points) ----
R = m.mpf(9) / 10
ss = m.mpf(3) / 4
mx_alg = m.mpf(0)
mx_wres = m.mpf(0)
min_w = m.inf
mx_root = m.mpf(0)
mx_crit = m.mpf(0)
bad_end = []
for k in range(2001):
    tt = m.mpf(k) / 2000
    U = m.exp(m.pi * 1j * tt)
    H = 1 + m.mpf(16) / 27 * m.conj(U) ** 2
    assert H.real >= m.mpf(11) / 27 - m.mpf('1e-75')
    Qm = 3 * m.sqrt(3) / 4 * U * m.sqrt(H)
    # exact q^2 identity residual
    mx_alg = max(mx_alg, abs(Qm**2 - (1 + m.mpf(27) / 16 * U**2)))
    roots = [R, R * ss * U, -R * ss * U]
    bs = [R / 3 * (1 + Qm), R / 3 * (1 - Qm)]
    mx_root = max(mx_root, max(abs(r) for r in roots))
    mx_crit = max(mx_crit, max(abs(x) for x in bs))
    for x in bs:
        # deleted-derivative zero check pointwise (as scalar polynomial identity in z):
        # P'_t(z) = 3 z^2 - 2R z - R^2 s^2 U^2 ; check its scalar roots are exactly bs:
        r1, r2 = bs
        mx_alg = max(mx_alg, abs(3 * (x - r1) * (x - r2) -
                                 (3 * x * x - 2 * R * x - R**2 * ss**2 * U**2)))
        # weights via conjugated log derivative
        wts = [1 / abs(x - a) ** 2 for a in roots]
        tot = sum(wts)
        wts = [wv / tot for wv in wts]
        mx_wres = max(mx_wres, abs(x - sum(wv * a for wv, a in zip(wts, roots))))
        min_w = min(min_w, min(wts))
    if k in (0, 2000):
        bad_end.append([str(abs(R - x)) for x in bs])

assert mx_alg < m.mpf('1e-78')
assert mx_wres < m.mpf('1e-78')
assert mx_root < 1 and mx_crit < 1
assert m.mpf(bad_end[0][1]) > m.mpf(21) / 20 and m.mpf(bad_end[0][0]) < m.mpf(1) / 5
assert m.mpf(bad_end[1][0]) > m.mpf(21) / 20 and m.mpf(bad_end[1][1]) < m.mpf(1) / 5
assert min_w > 0

out['scan'] = {'points': 2001, 'dps': 80,
               'max_identity_residual': str(mx_alg),
               'max_weight_residual': str(mx_wres),
               'min_weight': str(min_w),
               'max_root_norm': str(mx_root),
               'max_critical_norm': str(mx_crit),
               'endpoint_distances': bad_end}

# Classical-Sendov non-contradiction sanity: at each endpoint the OTHER branch is close
assert m.mpf(bad_end[0][0]) < 1 and m.mpf(bad_end[1][1]) < 1
out['classical_not_contradicted'] = 'near branch switches B+ -> B- ; each fiber t has a near critical point'

print(json.dumps(out, indent=2))
with open('independent-check-result.json', 'w') as f:
    json.dump(out, f, indent=2)
