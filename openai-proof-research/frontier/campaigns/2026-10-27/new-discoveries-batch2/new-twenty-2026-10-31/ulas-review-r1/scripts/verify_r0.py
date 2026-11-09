"""ulas-review-r1: independent certificate for the low coefficients r_{0,F}(m) (Section 5),
and polynomial-level checks of the whole chain r_j for m <= MMAX.
Low coefficients: [y^E]A_2 = sum_{i<=2E+1} tau_{m,i} [y^E]T(y^i), tau_{m,i} = [y^i]T_m(1+2y).
Degree bound (my derivation): deg_m [y^E]A_2 <= 4E+2, hence deg_m r_{0,F} <= 4F+6.
For m = q t + s, P(t) = r_{0,F}(q t + s) is integer valued of degree <= D, so
P(t) = sum_{i<=D} b_i binom(t,i), b_i = Delta^i P(0) in Z, and nu2(P(t)) >= min nu2(b_i) for every t >= 0."""
import math, sys
from fractions import Fraction
def v2(x):
    if x == 0: return 10**9
    x = abs(x); return (x & -x).bit_length() - 1
K = 12  # truncation order in y
def cheb_T_trunc(Nmax):
    """T_N(1+2y) mod y^K for N=0..Nmax (recurrence)."""
    out = [[1] + [0] * (K - 1), [1, 2] + [0] * (K - 2)]
    for N in range(2, Nmax + 1):
        a, b = out[-1], out[-2]
        c = [2 * a[i] + (4 * a[i - 1] if i else 0) - b[i] for i in range(K)]
        out.append(c)
    return out
def A2_low(m, Emax):
    TT = cheb_T_trunc(m + Emax + 3)
    tau = TT[m]
    res = []
    for E in range(Emax + 1):
        s = 0
        for i in range(0, min(2 * E + 1, K - 1) + 1):
            e, r = divmod(i, 2)
            if E - e < 0: continue
            if r == 0: t = TT[m + e][E - e]
            else:
                dd = TT[m + e + 1][E - e] - TT[m + e][E - e]; assert dd % 2 == 0; t = dd // 2
            s += tau[i] * t
        res.append(s)
    return res
def r0_low(m, Fmax):
    a = A2_low(m, Fmax + 1); d = a[:]; d[0] -= 1
    assert d[0] == 0
    r = []
    for F in range(Fmax + 1):
        r.append(d[F + 1] - (r[F - 1] if F >= 1 else 0))
    return r
fails = 0
def check(c, msg):
    global fails
    if not c: fails += 1; print("FAIL", msg)
# (c0) closed form of r_{0,0} for all m (degree <= 6 polynomial identity: check on 40 points)
for m in range(1, 41):
    check(3 * r0_low(m, 0)[0] == 2 * m * m * (m + 1) * (m + 5), f"r00 closed form m={m}")
print("c0: r_{0,0} = (2/3) m^2 (m+1)(m+5) on m=1..40 (degree<=6 => identity); fails", fails)
def binom_basis(q, s, F, D, extra=6):
    vals = [r0_low(q * t + s, F)[F] for t in range(D + 1 + extra)]
    diffs = []; cur = vals[:]
    for i in range(len(vals)):
        diffs.append(cur[0]); cur = [cur[j + 1] - cur[j] for j in range(len(cur) - 1)]
    return diffs
report = []
for F in (1, 2, 3):
    D = 4 * F + 6
    for (q, s) in [(4, 3), (16, 3), (16, 7), (16, 11), (16, 15), (4, 1)]:
        b = binom_basis(q, s, F, D)
        tail_zero = all(x == 0 for x in b[D + 1:])
        check(tail_zero, f"degree bound violated F={F} q={q} s={s}")
        vals = [v2(x) for x in b[:D + 1]]
        actual_deg = max(i for i, x in enumerate(b) if x != 0) if any(b) else -1
        report.append((F, q, s, actual_deg, vals[0], min(vals[1:]) if len(vals) > 1 else None, min(vals)))
        print(f"F={F} m={q}t+{s}: actual deg_t={actual_deg} (bound {D}); nu2(b_0)={vals[0]}, min nu2(b_i,i>=1)={min(vals[1:])}, min all={min(vals)}; tail zero={tail_zero}")
def get(F, q, s): return [r for r in report if r[0] == F and r[1] == q and r[2] == s][0]
# r130 claims
check(get(1, 4, 3)[6] >= 7 and get(2, 4, 3)[6] >= 7, "claim m=4t+3: r01, r02 >= 7")
check(get(1, 16, 15)[6] >= 11 and get(2, 16, 15)[6] >= 11, "claim m=16t+15: r01, r02 >= 11")
check(get(1, 16, 11)[4] == 7 and get(1, 16, 11)[5] >= 8, "claim m=16t+11: nu2(r01) = 7 exactly")
print("certificate claims (c1)-(c3); fails", fails)
# what the m=15 mod 16 argument actually needs: nu2(r01) >= 8 and nu2(r02) >= 9 (weights >= 7 after gains)
print("needed for m=15 mod 16: r01>=8, r02>=9 ->", get(1, 16, 15)[6] >= 8, get(2, 16, 15)[6] >= 9)
# --- Full chain at polynomial level, m <= MMAX, j <= J (consistency, not proof)
sys.setrecursionlimit(10000)
exec(open(sys.argv[1]).read().split("# --- power series helpers")[0])  # reuse MY OWN T from verify_operator.py
bl = lambda E: E.bit_length()
def omega(R): return min(v2(c) - bl(E) for E, c in enumerate(R) if c) if any(R) else 10**9
def div_y1y(P):
    P = trim(P[:]); assert P[0] == 0; P = P[1:]
    q = []; carry = 0
    for c in P: carry = c - carry; q.append(carry)
    assert q[-1] == 0; return trim(q[:-1]) if len(q) > 1 else [0]
MMAX, J = int(sys.argv[2]), int(sys.argv[3])
for m in range(1, MMAX + 1):
    A = [[1]]
    for j in range(J + 2): A.append(T(m, A[-1]))
    for j in range(J):
        r = div_y1y(trim(padd(A[j + 2], pscale(A[j], -1))))
        if m % 2 == 0:
            a = 3 + 2 * v2(m // 2) + j
            check(omega(r) >= a and v2(r[0]) == a, f"even chain m={m} j={j}")
            for i in range(1, 8):
                if 2 ** i - 1 < len(r): check(v2(r[2 ** i - 1]) >= a + i + 1, f"even invariant m={m} j={j} i={i}")
        elif m % 4 == 1:
            check(omega(r) >= 3 + j, f"m=1mod4 omega m={m} j={j}")
            if j == 0: check(v2(r[0]) == 3, f"m=1mod4 r00 m={m}")
        else:
            base = 7 if m % 16 == 15 else 6
            check(all(v2(c) >= base + j for c in r), f"m=3mod4 divisibility m={m} j={j}")
            if j >= 1: check(omega(r) >= base + j, f"m=3mod4 omega m={m} j={j}")
            if j == 0 and m % 16 in (3, 7): check(v2(r[0]) == 6 and all(v2(c) >= 7 for c in r[1:]), f"readout 3/7 m={m}")
            if j == 1 and m % 16 == 11: check(v2(r[0]) == 7 and all(v2(c) >= 8 for c in r[1:]), f"readout 11 m={m}")
print(f"chain checks m<={MMAX}, j<{J}; TOTAL FAILS", fails)
print("ALL_OK" if fails == 0 else "SOME_FAIL")
