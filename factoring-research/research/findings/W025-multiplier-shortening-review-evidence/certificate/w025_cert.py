"""W025 frozen certificate. Literal bounded search; NOT a Lenstra implementation."""
import json, sys
from fractions import Fraction

CAP = 20000
ev = [0]
def charge(n=1):
    ev[0] += n
    if ev[0] > CAP:
        raise RuntimeError("event cap exceeded")

def centered(a, m):
    a %= m
    return a - m if a > m // 2 else a

def cdiv(a, b):  # ceil for b>0
    return -((-a) // b)

def icbrt_ceil(n):
    lo, hi = 0, 1
    while hi ** 3 < n:
        hi *= 2
    while lo < hi:
        mid = (lo + hi) // 2
        if mid ** 3 >= n:
            hi = mid
        else:
            lo = mid + 1
    return lo

def val(c, ell):
    v = 0
    while c % ell == 0:
        c //= ell; v += 1
    return v

def peval(coef, x):
    return sum(a * x ** i for i, a in enumerate(coef))

def multiplier(d, K, Q, ell, active):
    """least c in [1,B] with |c d_i - Q k_i| <= (Q-1)//K_i for active i."""
    B = 1
    for i in active:
        B *= K[i]
    if B >= Q:
        return {"fallback": True, "B": B}
    for c in range(1, B + 1):
        charge()
        if all(abs(centered(c * d[i], Q)) <= (Q - 1) // K[i] for i in active):
            v = val(c, ell); r = ell ** v; cp = c // r; Qp = Q // r
            P = []
            for i in range(len(d)):
                if i in active:
                    e = centered(c * d[i], Q)
                    assert e % r == 0, "active error not divisible by r"
                    P.append(e // r)
                else:
                    P.append(centered(cp * d[i], Qp))
            return {"fallback": False, "B": B, "c": c, "v": v, "r": r, "cp": cp, "Qp": Qp, "P": P}
    return {"fallback": False, "B": B, "c": None}

viol = []
def check(cond, msg):
    if not cond:
        viol.append(msg)

def covered_S(Rx, sigma, Q, W):
    s0 = (sigma * Rx) % Q
    t = cdiv(-W - s0, Q)
    while s0 + Q * t <= W:
        yield s0 + Q * t
        t += 1

def generic_case(name, ell, Q, d, Z, T, W):
    w = [Z ** i for i in range(len(d))]
    active = [i for i in range(len(d)) if w[i] > T]
    K = {i: cdiv(w[i], T) for i in active}
    m = multiplier(d, K, Q, ell, active)
    out = {"case": name, "active": active, "K": K, **{k: m[k] for k in m}}
    if m.get("fallback") or m.get("c") is None:
        return out
    cp, Qp, P, B = m["cp"], m["Qp"], m["P"], m["B"]
    D = len(d)
    bound = cdiv(B * W, Q) + D * T
    for i in range(D):
        check((P[i] - cp * d[i]) % Qp == 0, f"{name}: P!=c'R coef {i}")
    check((P[0] - cp * d[0]) % ell == 0, f"{name}: P mod ell")
    maxtau = 0
    for x in range(-Z, Z + 1):
        Px = peval(P, x); Rx = peval(d, x)
        check(abs(Px) <= D * Qp * T, f"{name}: |P| bound x={x}")
        for sigma in (1, -1):
            for S in covered_S(Rx, sigma, Q, W):
                charge()
                num = cp * S - sigma * Px
                check(num % Qp == 0, f"{name}: divisibility x={x}")
                tau = num // Qp
                maxtau = max(maxtau, abs(tau))
                check(abs(tau) <= bound, f"{name}: tau bound x={x} S={S}")
    out.update(bound2=bound, maxtau=maxtau)
    return out

def chart_case(name, ell, h, p, q, v, U, V):
    N = p * q
    m = ell ** h; Q = m * m; a = cdiv(2 * h, 5); H = ell ** a
    u = (v * q * pow(p, -1, m)) % m
    assert 1 <= u <= U and u % ell and v % ell and (u * p - v * q) % m == 0
    W = U * p + V * q
    S_true = u * p + v * q
    u0 = u % H; v0 = v % H
    y0 = (v - v0) // H
    ylo = cdiv(-V - v0, H); yhi = (V - v0) // H
    assert ylo == yhi == y0, "not singleton signed chart"
    xlo = cdiv(1 - u0, H); xhi = (U - u0) // H
    Z = max(1, abs(xlo), abs(xhi))
    Dd = 4 * N * u0 * v0
    roots = [b for b in range(ell) if (b * b - Dd) % ell == 0]
    assert roots
    r0 = roots[0]
    for _ in range(4 * h + 4):
        r0 = (r0 - (r0 * r0 - Dd) * pow(2 * r0, -1, Q)) % Q
    assert (r0 * r0 - Dd) % Q == 0
    cs = [Fraction(1), Fraction(1, 2), Fraction(-1, 8), Fraction(1, 16), Fraction(-5, 128)]
    fm = lambda f: f.numerator * pow(f.denominator, -1, Q) % Q
    coef = [0] * 5
    for i in range(5):
        for j in range(5 - i):
            dij = r0 * fm(cs[i]) * fm(cs[j]) * H ** (i + j) * pow(u0, -i, Q) * pow(v0, -j, Q) % Q
            coef[i] = (coef[i] + dij * y0 ** j) % Q
    for x in range(xlo, xhi + 1):
        charge()
        check((peval(coef, x) ** 2 - 4 * N * (u0 + H * x) * (v0 + H * y0)) % Q == 0, f"{name}: R^2 x={x}")
    for i in range(5):
        check(coef[i] % (H ** i) == 0, f"{name}: coef {i} not divisible by H^{i}")
    A = max(1, cdiv(W, Q))
    out = {"case": name, "ell": ell, "h": h, "Q": Q, "H": H, "u": u, "v": v, "u0": u0, "v0": v0,
           "y0": y0, "xlo": xlo, "xhi": xhi, "Z": Z, "W": W, "A": A, "A_le_Z2": 1 <= A <= Z * Z}
    T = icbrt_ceil(A * Z ** 7)
    K = {3: cdiv(Z ** 3, T), 4: cdiv(Z ** 4, T)}
    check(Z * Z <= T <= Z ** 3, f"{name}: Z^2<=T<=Z^3")
    mres = multiplier(coef, K, Q, ell, [3, 4])
    B = mres["B"]
    check(B <= 4 * Z ** 7 // (T * T) and B * A <= 4 * T, f"{name}: B bounds")
    c_struct = Q // H ** 3
    struct_ok = all(abs(centered(c_struct * coef[i], Q)) <= (Q - 1) // K[i] for i in (3, 4))
    out.update(T=T, K=K, B=B, B_lt_Q=B < Q, c_struct=c_struct, c_struct_le_B=c_struct <= B,
               c_struct_feasible=struct_ok, multiplier={k: mres[k] for k in mres if k != "P"})
    x_t = (u - u0) // H
    sig_t = 1 if (S_true - peval(coef, x_t)) % Q == 0 else -1
    check((S_true - sig_t * peval(coef, x_t)) % Q == 0, f"{name}: true S root")
    eps = {s: (u0 + N * v0 - s * r0) % ell for s in (1, -1)}
    out.update(eps=eps, sigma_true=sig_t, p_mod_ell=p % ell)
    if not mres.get("fallback") and mres.get("c"):
        cp, Qp, P = mres["cp"], mres["Qp"], mres["P"]
        for i in range(5):
            check((P[i] - cp * coef[i]) % Qp == 0, f"{name}: P!=c'R {i}")
        maxtau = 0
        for x in range(-Z, Z + 1):
            check(abs(peval(P, x)) <= 3 * Qp * T, f"{name}: |P|<=3Q'T x={x}")
        for x in range(xlo, xhi + 1):
            Px, Rx = peval(P, x), peval(coef, x)
            uu, vv = u0 + H * x, v0 + H * y0
            for s in (1, -1):
                for tau_end in (-7 * T, 7 * T):
                    Ee = cp * (uu + N * vv) - s * Px - Qp * tau_end
                    check(Ee % ell == cp * eps[s] % ell, f"{name}: filter residue endpoint")
                for S in covered_S(Rx, s, Q, W):
                    charge()
                    num = cp * S - s * Px
                    check(num % Qp == 0, f"{name}: div")
                    tau = num // Qp
                    maxtau = max(maxtau, abs(tau))
                    check(abs(tau) <= 7 * T, f"{name}: |tau|<=7T")
                    Ee = cp * (uu + N * vv) - s * Px - Qp * tau
                    check(Ee % ell == cp * eps[s] % ell, f"{name}: filter residue")
                    if eps[s]:
                        check(Ee != 0, f"{name}: zero exponent retained")
        Px = peval(P, x_t)
        tau_t = (cp * S_true - sig_t * Px) // Qp
        E_t = cp * (u + N * v) - sig_t * Px - Qp * tau_t
        check(E_t == cp * (p - 1) * (v * q - u), f"{name}: true E'")
        out.update(maxtau=maxtau, sevenT=7 * T, true_retained=eps[sig_t] != 0, true_E_nonzero=E_t != 0,
                   P=P)
    # truncation baseline modulo H^3
    Q3 = H ** 3
    assert Q % Q3 == 0
    P3 = [centered(coef[i], Q3) for i in range(3)]
    b3 = (W + Q3 * Z * Z) // Q3
    mt3 = 0
    for x in range(xlo, xhi + 1):
        Rx, P3x = peval(coef, x), peval(P3, x)
        uu, vv = u0 + H * x, v0 + H * y0
        for s in (1, -1):
            for S in covered_S(Rx, s, Q, W):
                charge()
                num = S - s * P3x
                check(num % Q3 == 0, f"{name}: trunc div")
                t3 = num // Q3
                mt3 = max(mt3, abs(t3))
                check(abs(t3) <= b3, f"{name}: trunc tau bound")
                E3 = uu + N * vv - s * P3x - Q3 * t3
                check(E3 % ell == eps[s], f"{name}: trunc filter residue")
    out.update(trunc_Q3=Q3, trunc_bound=b3, trunc_maxtau=mt3, trunc_lt_7T=b3 < 7 * T)
    return out

res = {}
try:
    res["K1"] = chart_case("K1", 3, 5, 1013, 100003, -1, 242, 2)
    res["K2"] = chart_case("K2", 5, 4, 1009, 10007, 1, 624, 2)
    res["K3"] = generic_case("K3", 3, 3 ** 6, [1, 3, 6, 81, 81], 4, 16, 2 * 3 ** 6)
    res["K4"] = generic_case("K4", 3, 9, [1, 3, 3, 3, 3], 2, 4, 18)
    Z, A, Q = 4, 1, 9
    T = icbrt_ceil(A * Z ** 7)
    B = cdiv(Z ** 3, T) * cdiv(Z ** 4, T)
    res["K5"] = {"case": "K5", "T": T, "B": B, "fallback": B >= Q}
    status = "completed"
except Exception as e:
    status = f"aborted: {e!r}"
res["status"] = status
res["events"] = ev[0]
res["violations"] = viol
print(json.dumps(res, indent=1, default=str))
