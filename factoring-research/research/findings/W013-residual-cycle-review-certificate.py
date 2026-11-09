"""W013 residual-cycle review: fixed exact certificate (see -certificate-brief.md).

Standard library only. Fixed inputs; no timing, sweep or search. Run:
    python3 -I W013-residual-cycle-review-certificate.py > ...-certificate-output.json
"""
import itertools
import json
from math import gcd, isqrt

N = 22117019  # Gower--Wagstaff Section 3.4 example, = 4451 * 4969
out = {"N": N, "checks": {}, "failures": []}


def check(name, ok, detail=None):
    out["checks"][name] = {"ok": bool(ok), "detail": detail}
    if not ok:
        out["failures"].append(name)


# C1: (P+k b)^2 - N - b (a + 2kP + k^2 b) == P^2 - N - a b  as polynomials.
# Degree <= 2 in each of P, k, b and <= 1 in a, N; a 4-point grid per variable suffices.
grid = (-2, -1, 0, 3)
bad = 0
for P, k, b, a, n in itertools.product(grid, repeat=5):
    lhs = (P + k * b) ** 2 - n - b * (a + 2 * k * P + k * k * b)
    if lhs != P * P - n - a * b:
        bad += 1
check("C1_divided_norm_update_identity", bad == 0, {"grid_points": len(grid) ** 5, "mismatches": bad})

# C2: continued fraction / principal cycle, Gower--Wagstaff (2.2)-(2.4).
q0 = isqrt(N)


def cf_rows(count):
    """Return list of (n, P_n, Q_{n-1}, Q_n, q_n) for n = 1..count."""
    rows = []
    P, Qprev, Q = q0, 1, N - q0 * q0  # P_1, Q_0, Q_1
    n = 1
    while n <= count:
        q = (q0 + P) // Q
        rows.append((n, P, Qprev, Q, q))
        Pn = q * Q - P
        Qn = (N - Pn * Pn) // Q
        assert Qprev * Q == N - P * P
        P, Qprev, Q = Pn, Q, Qn
        n += 1
    return rows


table1 = {  # (i, first coeff, P, last coeff) from Gower--Wagstaff Table 1, i = 1..18
    1: (1, 4702, -8215), 2: (-8215, 3513, 1190), 3: (1190, 3627, -7531),
    4: (-7531, 3904, 913), 5: (913, 4313, -3850), 6: (-3850, 3387, 2765),
    7: (2765, 2143, -6338), 8: (-6338, 4195, 713), 9: (713, 4361, -4346),
    10: (-4346, 4331, 773), 11: (773, 4172, -6095), 12: (-6095, 1923, 3022),
    13: (3022, 4121, -1699), 14: (-1699, 4374, 1757), 15: (1757, 4411, -1514),
    16: (-1514, 4673, 185), 17: (185, 4577, -6314), 18: (-6314, 1737, 3025),
}
rows = cf_rows(18)
forms = {n: ((-1) ** (n - 1) * Qp, P, (-1) ** n * Q) for (n, P, Qp, Q, q) in rows}
check("C2_table1_reproduced", all(forms[i] == table1[i] for i in table1),
      {i: forms[i] for i in (1, 17, 18)})

# Card update, sign-corrected forward step, and the literal "P'=P+kb nearest below sqrt N".
fwd_ok, literal_k0, reduced_all, rev_plus, rev_minus = True, True, True, True, True
for (n, P, Qp, Q, q) in rows[:-1]:
    a, _, b = forms[n]
    nxt = forms[n + 1]
    # forward: P_{n+1} = -P + q*Q. In Card parametrization P' = P + k b equals -P_{n+1}.
    Pp = -(q * Q - P)
    k, r = divmod(Pp - P, b)
    c = a + 2 * k * P + k * k * b
    fwd_ok &= (r == 0 and (Pp * Pp - N) % b == 0 and (Pp * Pp - N) // b == c
               and nxt[0] == b and c == nxt[2])
    # reducedness: sqrt(N)-|b| < P < sqrt(N)  <=>  integer form below
    red = P <= q0 and (P + abs(b)) > q0  # sqrt(N) irrational
    reduced_all &= red
    # unique P' = P (mod |b|) in (sqrt N - |b|, sqrt N): it is P itself, giving k=0, c=a
    cands = [x for x in range(q0 - abs(b) + 1, q0 + 1) if (x - P) % abs(b) == 0]
    literal_k0 &= (cands == [P]) and (a + 0 == (P * P - N) // b)
    # reverse-edge labels
    ia, ib = pow(a, -1, N), pow(b, -1, N)
    rev_plus &= (P * ia * P * ib) % N == 1
    rev_minus &= (P * ia * (-P) * ib) % N == N - 1
check("C2_sign_corrected_card_update_matches_rho", fwd_ok)
check("C2_rows_reduced", reduced_all)
check("C2_literal_nearest_below_sqrtN_choice_is_k0_backtrack", literal_k0)
check("C2_reverse_edge_label_plus_one", rev_plus)
check("C2_reverse_edge_label_minus_one", rev_minus)

# Labels vs convergent numerators: A_0=1, A_1=q0, A_n = q_{n-1} A_{n-1} + A_{n-2}.
A, B = [1, q0], [0, 1]
for (n, P, Qp, Q, q) in rows:
    A.append(q * A[-1] + A[-2])
    B.append(q * B[-1] + B[-2])
norm_ok = all(A[n] ** 2 - N * B[n] ** 2 == (-1) ** n * rows[n - 1][3] for n in range(1, 19))
# exact multiplicative recurrence in Z[sqrt N]: (A_n + B_n s) Q_{n-1} = (A_{n-1}+B_{n-1}s)(P_n + s)
rec_ok = all(A[n] * rows[n - 1][2] == A[n - 1] * rows[n - 1][1] + B[n - 1] * N
             and B[n] * rows[n - 1][2] == A[n - 1] + B[n - 1] * rows[n - 1][1]
             for n in range(1, 19))
lab_ok, L, signs = True, 1, []
for (n, P, Qp, Q, q) in rows:
    a = forms[n][0]
    L = L * P * pow(a, -1, N) % N
    sgn = 1 if L == A[n] % N else (-1 if L == (-A[n]) % N else 0)
    signs.append(sgn)
    lab_ok &= sgn != 0
check("C2_convergent_norm_identity", norm_ok)
check("C2_convergent_multiplicative_recurrence", rec_ok)
check("C2_card_label_product_is_plus_minus_A_n", lab_ok, {"signs_n1_to_18": signs})

# C3: one full principal form cycle; first-coefficient collisions.
cyc, P, Qprev, Q, n = [], q0, 1, N - q0 * q0, 1
start = None
while True:
    f = ((-1) ** (n - 1) * Qprev, P, (-1) ** n * Q)
    if start is None:
        start = f
    elif f == start:
        break
    cyc.append((n, f))
    q = (q0 + P) // Q
    Pn = q * Q - P
    Qn = (N - Pn * Pn) // Q
    P, Qprev, Q = Pn, Q, Qn
    n += 1
T = len(cyc)
ell = next(m for (m, f) in cyc if abs(f[2]) == 1)  # CF period: first n with Q_n = 1
# prefix label Lam[n-1]^2 = a_n (a_1 = 1)
Lam, Lcur = [1], 1
for (m, f) in cyc:
    Lcur = Lcur * f[1] * pow(f[0], -1, N) % N
    Lam.append(Lcur)
unit = Lam[ell]
sq_ok = all(Lam[m - 1] * Lam[m - 1] % N == cyc[m - 1][1][0] % N for m in range(1, T + 1))
nonunit_coeffs = sorted({abs(f[0]) for (m, f) in cyc if gcd(f[0], N) != 1})
first = {}
coll = []
for (m, f) in cyc:
    first.setdefault(f[0], []).append((m, f[1]))
E = {pow(unit, e, N) for e in range(4)} | {(-pow(unit, e, N)) % N for e in range(4)}
counts = {"same_ideal": 0, "conjugate": 0, "mixed": 0, "small_|a|<=2": 0}
conj_in_E, conj_total, mixed_proper, conj_proper, all_sq1 = True, 0, 0, 0, True
examples = []
for a, lst in first.items():
    for (i, Pi), (j, Pj) in itertools.combinations(lst, 2):
        u = Lam[j - 1] * pow(Lam[i - 1], -1, N) % N
        all_sq1 &= u * u % N == 1
        g = (gcd(u - 1, N), gcd(u + 1, N))
        proper = any(1 < x < N for x in g)
        m_ = abs(a)
        if m_ <= 2:
            kind = "small_|a|<=2"
        elif (Pi - Pj) % m_ == 0:
            kind = "same_ideal"
        elif (Pi + Pj) % m_ == 0:
            kind = "conjugate"
        else:
            kind = "mixed"
        counts[kind] += 1
        if kind == "conjugate":
            conj_total += 1
            conj_in_E &= u in E
            conj_proper += proper
        if kind == "mixed":
            mixed_proper += proper
        if len(examples) < 12 or (kind == "mixed" and proper and len(examples) < 20):
            examples.append({"a": a, "i": i, "j": j, "Pi": Pi, "Pj": Pj, "kind": kind,
                             "u": u, "gcds": g})
check("C3_prefix_label_squares_equal_coefficients", sq_ok)
check("C3_all_collision_ratios_square_to_one", all_sq1)
check("C3_no_same_ideal_collision_within_cycle", counts["same_ideal"] == 0)
check("C3_conjugate_collisions_in_unit_image_group", conj_in_E)
out["C3"] = {
    "form_cycle_length_T": T, "cf_period_ell": ell, "unit_image_mod_N": unit,
    "unit_image_squared_mod_N": unit * unit % N,
    "unit_image_gcds": (gcd(unit - 1, N), gcd(unit + 1, N)),
    "coefficients_sharing_factor_with_N": nonunit_coeffs,
    "collision_counts": counts, "conjugate_proper": conj_proper,
    "mixed_proper": mixed_proper, "examples": examples,
    "note": "descriptive single-N counts; not performance or probability evidence",
}

# C4: raw ceil-square recurrence, 40 steps from a0 = 1.
a, R, raw = 1, 1, []
raw_ok = True
for step in range(40):
    t = isqrt((N - 1) // a) + 1
    b = a * t * t - N
    raw_ok &= a * (t - 1) ** 2 < N <= a * t * t
    raw_ok &= b < a or (b - a) ** 2 < 4 * N * a
    if b == 0 or gcd(b, N) != 1:
        raw.append({"step": step, "a": a, "t": t, "b": b, "stop": "zero_or_nonunit"})
        break
    R = R * t % N
    raw_ok &= (b - R * R) % N == 0
    raw.append({"step": step, "a": a, "t": t, "b": b, "log2_b": b.bit_length()})
    a = b
check("C4_raw_recurrence_identities", raw_ok)
out["C4"] = {"steps": raw[:6] + raw[-4:], "bitlen_N": N.bit_length(),
             "max_state_bits": max(r["b"].bit_length() for r in raw)}

# C5: square-root multiplicities.
def factor_small(m):
    f, d = {}, 2
    while d * d <= m:
        while m % d == 0:
            f[d] = f.get(d, 0) + 1
            m //= d
        d += 1
    if m > 1:
        f[m] = f.get(m, 0) + 1
    return f


c5 = {}
c5_ok = True
for M in (15, 45, 105, 60, 120, 77):
    f = factor_small(M)
    v2 = f.get(2, 0)
    r_pred = 2 ** len([p for p in f if p != 2]) * (1 if v2 <= 1 else 2 if v2 == 2 else 4)
    units = [x for x in range(M) if gcd(x, M) == 1]
    roots = {}
    for x in units:
        roots.setdefault(x * x % M, []).append(x)
    sqrt1 = sorted(roots[1])
    counts_ = {len(v) for v in roots.values()}
    coset_ok = all(sorted(v[0] * s % M for s in sqrt1) == sorted(v) for v in roots.values())
    gcd_ok = all(1 < gcd(u - 1, M) < M for u in sqrt1 if u not in (1, M - 1))
    ok = counts_ == {r_pred} and coset_ok and gcd_ok and len(roots) * r_pred == len(units)
    c5_ok &= ok
    c5[M] = {"phi": len(units), "unit_squares": len(roots), "r": r_pred,
             "nontrivial_fraction": (r_pred - 2) / r_pred if r_pred >= 2 else 0.0, "ok": ok}
check("C5_root_multiplicity_formula", c5_ok)
out["C5"] = c5

print(json.dumps(out, indent=1, sort_keys=True))
