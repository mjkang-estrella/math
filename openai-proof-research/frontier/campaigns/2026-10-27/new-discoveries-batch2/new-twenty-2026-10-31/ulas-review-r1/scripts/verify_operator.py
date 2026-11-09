"""ulas-review-r1: independent check of the r130 operator framework (Sections 2-3, 5 formulas).
My own derivation: T(F) := U_2(w^m F) on Z[y], y=x/(1-x), w=1+2y, U_2 = even section.
  T(y^{2e})   = y^e T_{m+e}(1+2y)
  T(y^{2e+1}) = y^e (T_{m+e+1} - T_{m+e})(1+2y) / 2
All checks against honest power series in x (exact integers)."""
import sys, random, math
random.seed(342364)
def v2(x):
    if x == 0: return 10**9
    x = abs(x); return (x & -x).bit_length() - 1
def padd(a, b):
    n = max(len(a), len(b)); return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
def pscale(a, c): return [c * t for t in a]
def pmul(a, b):
    r = [0] * (len(a) + len(b) - 1)
    for i, s in enumerate(a):
        if s:
            for j, t in enumerate(b): r[i + j] += s * t
    return r
def trim(a):
    a = a[:]
    while len(a) > 1 and a[-1] == 0: a.pop()
    return a
def shift(a, e): return [0] * e + a
CT, CU = {}, {}
def chebT(N):  # T_N(1+2y) in Z[y]
    if N not in CT:
        if N == 0: CT[0] = [1]
        elif N == 1: CT[1] = [1, 2]
        else: CT[N] = trim(padd(pscale(pmul([1, 2], chebT(N - 1)), 2), pscale(chebT(N - 2), -1)))
    return CT[N]
def chebU(N):
    if N not in CU:
        if N == 0: CU[0] = [1]
        elif N == 1: CU[1] = [2, 4]
        else: CU[N] = trim(padd(pscale(pmul([1, 2], chebU(N - 1)), 2), pscale(chebU(N - 2), -1)))
    return CU[N]
def T_mono(m, E):
    e, r = divmod(E, 2)
    if r == 0: return shift(chebT(m + e), e)
    d = padd(chebT(m + e + 1), pscale(chebT(m + e), -1))
    assert all(c % 2 == 0 for c in d), "odd coefficient in T_{N+1}-T_N"
    return shift([c // 2 for c in d], e)
def T(m, F):
    out = [0]
    for E, c in enumerate(F):
        if c: out = padd(out, pscale(T_mono(m, E), c))
    return trim(out)
# --- power series helpers
def ser_C_pow(m, L):
    f = [1] + [0] * (L - 1)
    for _ in range(m):
        for s in [1] + [2 ** i for i in range(0, L.bit_length() + 1) if 2 ** i < L]:
            for n in range(s, L): f[n] += f[n - s]
    return f
def ser_poly_y(F, L):  # F(y(x)) as series in x, y = x/(1-x)
    out = [0] * L; cur = [1] + [0] * (L - 1)
    for E, c in enumerate(F):
        if E > 0:
            cur = [0] + cur[:-1]
            for n in range(1, L): cur[n] += cur[n - 1]
        if c:
            for n in range(L): out[n] += c * cur[n]
    return out
def smul(a, b, L):
    r = [0] * L
    for i in range(L):
        if a[i]:
            ai = a[i]
            for j in range(L - i): r[i + j] += ai * b[j]
    return r
fails = 0
def check(cond, msg):
    global fails
    if not cond:
        fails += 1; print("FAIL", msg)
# 1. T agrees with U_2(C^m F) = C^m T(F)
L = 80
for m in range(1, 13):
    Cm = ser_C_pow(m, 2 * L)
    Cm_half = Cm[:L]
    for trial in range(6):
        F = [random.randint(-50, 50) for _ in range(random.randint(1, 9))]
        lhs = smul(Cm, ser_poly_y(F, 2 * L), 2 * L)[0::2][:L]
        rhs = smul(Cm_half, ser_poly_y(T(m, F), L), L)
        check(lhs == rhs, f"T vs series m={m} F={F}")
print("1. T(F) = U_2(w^m F) verified against series: m<=12, 6 random F each, x^<80; fails so far", fails)
# 2. readout identity (1): c_m(4*2^j o) - c_m(2^j o) = [x^o] C^m d_j, d_j = A_{j+2}-A_j
L2 = 4 * 8 * 40 + 1
for m in range(1, 17):
    Cm = ser_C_pow(m, L2)
    A = [[1]]
    for j in range(5): A.append(T(m, A[-1]))
    for j in range(3):
        d = trim(padd(A[j + 2], pscale(A[j], -1)))
        ser = smul(Cm[:41], ser_poly_y(d, 41), 41)
        for o in range(1, 41):
            n = 2 ** j * o
            check(Cm[4 * n] - Cm[n] == ser[o], f"readout m={m} j={j} o={o}")
        # divisibility of d_j by y(1+y)
        q = []; rem = d[:]  # divide by y + y^2
        check(rem[0] == 0, f"d_j(0)!=0 m={m} j={j}")
        check(sum((-1) ** E * c for E, c in enumerate(rem)) == 0, f"d_j(-1)!=0 m={m} j={j}")
print("2. identity (1) for m<=16, j<=2, o<=40, and d_j(0)=d_j(-1)=0; fails so far", fails)
# 3. Lemma R: T(y(1+y) y^E) = y(1+y) Ttilde(y^E), with the r130 binomial forms
def Ttil_r130(m, E):
    e, r = divmod(E, 2)
    if r == 0:
        N = m + e; return shift([2 * 4 ** i * math.comb(N + i + 1, 2 * i + 1) for i in range(N + 1)], e)
    N = m + e; return shift([4 ** i * math.comb(N + i + 1, 2 * i) for i in range(N + 2)], e)
def div_y1y(P):  # exact division by y + y^2 in Z[y]
    P = trim(P[:]); assert P[0] == 0; P = P[1:]  # divide by y
    q = [0] * max(1, len(P) - 1 + 1)
    # divide by (1+y): synthetic
    q = []; carry = 0
    for c in P:
        carry = c - carry; q.append(carry)
    assert q[-1] == 0, "not divisible by 1+y"
    return trim(q[:-1]) if len(q) > 1 else [0]
for m in range(1, 41):
    for E in range(0, 16):
        lhs = T(m, shift([1, 1], E + 1))
        rhs = pmul([0, 1, 1], Ttil_r130(m, E))
        check(trim(lhs) == trim(rhs), f"Lemma R m={m} E={E}")
        # Chebyshev form 2 y^e U_{m+e} and y^e (U_{m+e+1}-U_{m+e})
        e, r = divmod(E, 2)
        cheb = shift(pscale(chebU(m + e), 2), e) if r == 0 else shift(trim(padd(chebU(m + e + 1), pscale(chebU(m + e), -1))), e)
        check(trim(cheb) == trim(Ttil_r130(m, E)), f"U-expansion m={m} E={E}")
print("3. Lemma R (binomial and Chebyshev-U forms) m<=40, E<=15; fails so far", fails)
# 4. T' rules for odd and even m: T(2(1+y)y^E) = 2(1+y) T'(y^E)
def Tp_r130(m, E):
    e, r = divmod(E, 2)
    if r == 0: return shift([4 ** i * math.comb(m + e + i, 2 * i) for i in range(m + e + 1)], e)
    return shift(pscale(chebU(m + e), 2), e + 1)
for m in range(1, 41):
    for E in range(0, 16):
        lhs = T(m, pscale(shift([1, 1], E), 2))
        rhs = pmul([2, 2], Tp_r130(m, E))
        check(trim(lhs) == trim(rhs), f"T' m={m} E={E}")
print("4. T' rules m<=40, E<=15; fails so far", fails)
# 5. Lemma W per-monomial gains: for monomial y^E (weight -bitlen(E) for coefficient 1)
bl = lambda E: E.bit_length()
worst = {}
for m in range(1, 97):
    for E in range(0, 70):
        P = Ttil_r130(m, E); e, r = divmod(E, 2)
        main = {}
        if r == 1: main[e] = 1
        if E == 0: main[0] = 2 * (m + 1)
        for F, c in enumerate(P):
            h = c - main.get(F, 0)
            g = v2(h) - bl(F) + bl(E)          # gain of the H part
            check(g >= 2, f"Lemma W H-gain<2 m={m} E={E} F={F}")
        for F, c in main.items():
            check(v2(c) - bl(F) + bl(E) >= 1, f"Lemma W main gain m={m} E={E}")
        gmin = min(v2(c) - bl(F) + bl(E) for F, c in enumerate(P) if c)
        key = ("E=0" if E == 0 else "odd" if r else "even>=2")
        if key == "E=0": gmin_claim = min(1 + v2(m + 1), 2)
        else: gmin_claim = 1 if r else 2
        check(gmin >= gmin_claim, f"per-monomial gain m={m} E={E} got {gmin} claim {gmin_claim}")
print("5. Lemma W monomial gains m<=96, E<=69; fails so far", fails)
# 6. exact [y^0] Ttilde(R) = 2(m+1)R_0 + R_1
for m in range(1, 30):
    R = [random.randint(-99, 99) for _ in range(12)]
    out = [0]
    for E, c in enumerate(R): out = padd(out, pscale(Ttil_r130(m, E), c))
    check(out[0] == 2 * (m + 1) * R[0] + R[1], f"constant term m={m}")
print("6. constant term formula; fails so far", fails)
# 7. U_N(1+t) and U_{N+1}-U_N binomial expansions, Pell, and the binomial identity of Section 4
for N in range(0, 60):
    for i in range(N + 2):
        pass
for k in range(1, 200):
    for a in range(0, k + 3):
        lhs = math.comb(k + a, 2 * a + 1) * (2 * a + 1) * math.comb(2 * a, a)
        rhs = k * math.comb(k + a, a) * math.comb(k - 1, a)
        check(lhs == rhs, f"binomial identity k={k} a={a}")
for k in range(1, 40):
    m = 2 * k
    lhs = trim(padd(chebT(m), [-1]))
    rhs = pmul([0, 1, 1], pscale(pmul(chebU(k - 1), chebU(k - 1)), 8))
    check(lhs == trim(rhs), f"Pell T_2k - 1 = 8 y(1+y) U_(k-1)^2 k={k}")
for h in range(0, 40):
    m = 2 * h + 1
    W = trim(padd(chebU(h), pscale(chebU(h - 1), -1))) if h >= 1 else [1]
    check(trim(padd(chebT(m), [1])) == trim(pmul([2, 2], pmul(W, W))), f"T_m+1 = 2(1+y)W_h^2 h={h}")
print("7. binomial identity k<200, Pell k<40, odd factorisation h<40; TOTAL FAILS", fails)
print("ALL_OK" if fails == 0 else "SOME_FAIL")
