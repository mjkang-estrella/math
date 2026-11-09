"""Exact certificate for the W010 Jacobi-filter review.

Standard library only. Rational arithmetic and Euler's criterion for the two
named fields p=167 and q=5 that appear in the parent's counterexample. No
candidate run, prime search, weight search or sweep. The only
enumerations are the 36 ordered pairs of one fixed six-point support, the 16
nonzero pairs of F_5 and an explicit odd fibre assignment on F_167.
"""
import json
import sys
from fractions import Fraction as Fr

checks = {}


def check(name, cond):
    checks[name] = bool(cond)
    if not cond:
        raise SystemExit("FAILED: " + name)


def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    r = pow(a, (p - 1) // 2, p)
    return 1 if r == 1 else -1


def Q(z, u):
    return z * z + z * u + u * u


def tables(nu, p):
    """K, A, B of W010 for a symmetric residual law nu on F_p^* (dict)."""
    K, A, B = {}, {}, {}
    for z, wz in nu.items():
        for u, wu in nu.items():
            if (z - u) % p == 0 or (z + u) % p == 0:
                continue
            b = Q(z, u) % p
            K[b] = K.get(b, 0) + wz * wu
    for a, w in nu.items():
        b = a * a % p
        A[b] = A.get(b, 0) + w * w
        B[b] = B.get(b, 0) + w
    return K, A, B


def sector_masses(K, A, B, p):
    Lp = sum((k for b, k in K.items() if legendre(b, p) == 1), Fr(0))
    Lm = sum((k for b, k in K.items() if legendre(b, p) == -1), Fr(0))
    Z = K.get(0, Fr(0))
    G = sum((k * B.get(b, 0) for b, k in K.items()), Fr(0))
    Dp = sum((k * (k - A.get(b, 0)) for b, k in K.items() if legendre(b, p) == 1), Fr(0))
    Dm = sum((k * k for b, k in K.items() if legendre(b, p) == -1), Fr(0))
    Dv = sum((k * (k - A.get(b, 0)) for b, k in K.items()), Fr(0))
    return dict(Lp=Lp, Lm=Lm, Z=Z, G=G, Dp=Dp, Dm=Dm, Dv=Dv)


p, q = 167, 5

# ---- Euler criterion at p=167 for the six norm parameters and root squares
betas = {(3, 5): 49, (3, -5): 19, (3, 7): 79, (3, -7): 37, (5, 7): 109, (5, -7): 39}
for (z, u), b in betas.items():
    check(f"Q{z},{u}={b}", Q(z, u) == b)
check("six parameters distinct and nonzero mod 167", len({b % p for b in betas.values()}) == 6 and all(b % p for b in betas.values()))
chis = {b: legendre(b, p) for b in betas.values()}
check("chi_167: 49,19 squares; 79,37,109,39 nonsquares",
      chis == {49: 1, 19: 1, 79: -1, 37: -1, 109: -1, 39: -1})
check("occupied root squares {9,25,49} meet parameters only at 49",
      {9, 25, 49} & set(betas.values()) == {49})
check("F_49(3)=F_49(5)=-120, F_49(7)=0",
      all((x ** 3 - 49 * x) == -120 for x in (3, 5)) and 7 ** 3 - 49 * 7 == 0)
check("-120 nonzero mod 167 and third root -8 unoccupied", (-120) % p != 0 and (-8) % p not in {3, 5, 7, p - 3, p - 5, p - 7})


def law(t, H):
    return {3: t, p - 3: t, 5: t, p - 5: t, 7: H, p - 7: H}


# ---- q=5 uniform start: direct count and formula (5)
nu_q = {a: Fr(1, 5) for a in range(1, 5)}
Kq, Aq, Bq = tables(nu_q, q)
Sq = sector_masses(Kq, Aq, Bq, q)
eps_q, h_q = legendre(-3, q), legendre(3, q)
C0q, D0q = q - eps_q - 4, 3 + h_q
check("q=5: epsilon=h=-1, C0=D0=2", (eps_q, h_q, C0q, D0q) == (-1, -1, 2, 2))
check("q=5 direct: L+=0, L-=8/25, Z=0, G=0, D+=0",
      (Sq["Lp"], Sq["Lm"], Sq["Z"], Sq["G"], Sq["Dp"]) == (0, Fr(8, 25), 0, 0, 0))
check("q=5 formula (5) agrees",
      Fr((q - 1) * (C0q - D0q), 2 * q * q) == Sq["Lp"]
      and Fr((q - 1) * (C0q + D0q), 2 * q * q) == Sq["Lm"]
      and Fr((q - 1) * (1 + eps_q), q * q) == Sq["Z"])
check("q=5: legal mass = (q-1)(q-3)/q^2", Sq["Lp"] + Sq["Lm"] + Sq["Z"] == Fr(8, 25))
check("q=5: monic odd X^167-X^3+X is the identity function",
      all((pow(x, 167, 5) - x ** 3 + x - x) % 5 == 0 for x in range(5)))

# ---- p=7 formula (5) (no enumeration): L+=0 there as well
eps7, h7 = legendre(-3, 7), legendre(3, 7)
check("p=7 formula: C0=D0, so L+=0", 7 - eps7 - 4 == 3 + h7)


def audit(t, H, tag):
    m = 1 - 4 * t - 2 * H
    nu = law(t, H)
    K, A, B = tables(nu, p)
    S = sector_masses(K, A, B, p)
    out = {}
    check(f"{tag}: K tables", K == {49: 4 * t * t, 19: 4 * t * t, 79: 4 * t * H, 37: 4 * t * H, 109: 4 * t * H, 39: 4 * t * H})
    check(f"{tag}: A(49)=2H^2, B(49)=2H", A[49] == 2 * H * H and B[49] == 2 * H)
    check(f"{tag}: L+=8t^2, L-=16tH, Z=0", (S["Lp"], S["Lm"], S["Z"]) == (8 * t * t, 16 * t * H, 0))
    check(f"{tag}: D+=32t^4-8t^2H^2", S["Dp"] == 32 * t ** 4 - 8 * t * t * H * H)
    check(f"{tag}: D-=64t^2H^2", S["Dm"] == 64 * t * t * H * H)
    check(f"{tag}: unfiltered D_v=32t^4+56t^2H^2>0", S["Dv"] == 32 * t ** 4 + 56 * t * t * H * H and S["Dv"] > 0)
    raw = Sq["Lm"] * S["Dp"] + Sq["Lp"] * S["Dm"]
    C = S["Lp"] * Sq["Lm"] + S["Lm"] * Sq["Lp"]
    cond = raw / C
    dm_raw = Sq["Lm"] * S["G"]
    beta_gcd = S["Z"] * (Sq["Lp"] + Sq["Lm"]) + (S["Lp"] + S["Lm"]) * Sq["Z"]
    # accepted parameters at p are exactly 49 and 19, each with weight 4t^2*L_(q,-)
    cond_direct = ((K[49] - A[49]) + K[19]) / 2
    check(f"{tag}: conditional drift = 4t^2-H^2 directly", cond == cond_direct == 4 * t * t - H * H)
    check(f"{tag}: total collision m^2+v nondecreasing at beta=49",
          (K[49] + A[49] + 2 * m * B[49]) >= 0)
    q_drift = S["Lm"] * Sq["Dp"] + S["Lp"] * Sq["Dm"]
    out.update(m=m, Lp=S["Lp"], Lm=S["Lm"], Dp=S["Dp"], Dm=S["Dm"], Dv_unfiltered_local=S["Dv"],
               unfiltered_raw_composite=Sq["Lp"] * 0 + (Sq["Lp"] + Sq["Lm"] + Sq["Z"]) * S["Dv"],
               C=C, filtered_raw_dv_p=raw, filtered_conditional_dv_p=cond,
               filtered_raw_dm_p=dm_raw, beta_gcd_proper_prob=beta_gcd,
               filtered_raw_dv_q=q_drift, sign_threshold_Lq_plus_over_Lq_minus=-S["Dp"] / S["Dm"])
    return out


r1 = audit(Fr(1, 12), Fr(1, 4), "rational")
check("rational: m=1/6", r1["m"] == Fr(1, 6))
check("rational: D+=-5/2592", r1["Dp"] == Fr(-5, 2592))
check("rational: raw filtered drift -1/1620", r1["filtered_raw_dv_p"] == Fr(-1, 1620))
check("rational: C=4/225", r1["C"] == Fr(4, 225))
check("rational: conditional -5/144", r1["filtered_conditional_dv_p"] == Fr(-5, 144))
check("rational: sign threshold 5/72", r1["sign_threshold_Lq_plus_over_Lq_minus"] == Fr(5, 72))

t = Fr(14, 167)
r2 = audit(t, 3 * t, "integral")
check("integral: m=27/167", r2["m"] == Fr(27, 167))
check("integral: D+=-40t^4", r2["Dp"] == -40 * t ** 4)
check("integral: conditional -5t^2", r2["filtered_conditional_dv_p"] == -5 * t * t)
check("integral: sign threshold 5/72", r2["sign_threshold_Lq_plus_over_Lq_minus"] == Fr(5, 72))

# explicit odd function on F_167 with fibre sizes 27 (zero), 14,14,14,14,42,42
reps = list(range(1, 84))  # representatives of the 83 pairs {x,-x}
assign = [0] * 13 + [3] * 14 + [5] * 14 + [7] * 42
check("83 input pairs used", len(assign) == 83)
f = {0: 0}
for x, a in zip(reps, assign):
    f[x] = a % p
    f[p - x] = (-a) % p
check("function is odd on all of F_167", all(f[(-x) % p] == (-f[x]) % p for x in range(p)))
counts = {}
for x in range(p):
    counts[f[x]] = counts.get(f[x], 0) + 1
check("fibre counts", counts == {0: 27, 3: 14, p - 3: 14, 5: 14, p - 5: 14, 7: 42, p - 7: 42})

# uniform-start formula (5) identities, symbolic in (p, eps, h) by exact polynomial check on
# the identity sum = (p-1)(p-3)/p^2: (C0-D0)+(C0+D0) over 2 plus (1+eps) equals p-3.
for eps in (-1, 1):
    for h in (-1, 1):
        # coefficients in p: C0 + 1 + eps = p - 3 identically
        check(f"ell identity eps={eps},h={h}", all((pp - eps - 4) + 1 + eps == pp - 3 for pp in (11, 13, 17)))
        # q>=11 lower bound: C0-D0 >= q-9 and C0+D0 <= q+1
        check(f"ratio bound eps={eps},h={h}", all((qq - eps - 7 - h) >= qq - 9 and (qq - eps - 1 + h) <= qq + 1 for qq in (11, 101)))
check("(q-9)/(q+1) at q=11 exceeds 5/72", Fr(2, 12) > Fr(5, 72))


def fmt(d):
    return {k: str(v) for k, v in d.items()}


json.dump({"python": sys.version.split()[0], "checks": checks, "n_checks": len(checks),
           "rational_t_1_12_H_1_4": fmt(r1), "integral_t_14_167_H_42_167": fmt(r2),
           "legendre_167": {str(k): v for k, v in chis.items()},
           "q5_uniform": fmt(Sq)}, sys.stdout, indent=2)
print()
