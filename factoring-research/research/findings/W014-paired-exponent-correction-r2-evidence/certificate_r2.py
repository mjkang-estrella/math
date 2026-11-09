"""W014 Card C round 2 fixed algebra certificate (preregistered; run once).

Every input is a fixed constant from preregistration.md. Failures are recorded
in the JSON output and make the exit code 1; nothing is retried or filtered.
"""
import json
import math
import sys
from fractions import Fraction

RESULTS = {"checks": {}, "failures": []}


def record(name, ok, detail):
    RESULTS["checks"].setdefault(name, []).append({"ok": bool(ok), **detail})
    if not ok:
        RESULTS["failures"].append({"check": name, **detail})


def legendre(a, p):
    a %= p
    if a == 0:
        return 0
    return 1 if pow(a, (p - 1) // 2, p) == 1 else -1


def jacobi(a, n):
    a %= n
    result = 1
    while a:
        while a % 2 == 0:
            a //= 2
            if n % 8 in (3, 5):
                result = -result
        a, n = n, a
        if a % 4 == 3 and n % 4 == 3:
            result = -result
        a %= n
    return result if n == 1 else 0


# ---- arithmetic in R = (Z/M)[t]/(t^2 - d) -------------------------------
def rmul(a, b, d, m):
    return ((a[0] * b[0] + d * a[1] * b[1]) % m, (a[0] * b[1] + a[1] * b[0]) % m)


def rpow(a, e, d, m):
    if e < 0:  # only used for norm-one elements: inverse = conjugate
        a, e = (a[0], (-a[1]) % m), -e
    r, b = (1 % m, 0), a
    while e:
        if e & 1:
            r = rmul(r, b, d, m)
        b = rmul(b, b, d, m)
        e >>= 1
    return r


def cayley(a, d, m):
    den = (a * a - d) % m
    inv = pow(den, -1, m)
    return ((a * a + d) * inv % m, 2 * a * inv % m)


# ---- direct product G x T: elements (U, (x, y)) -------------------------
def gmul(A, B, d, m):
    return (A[0] * B[0] % m, rmul(A[1], B[1], d, m))


def gpow(A, e, d, m):
    U = pow(A[0], e, m) if e >= 0 else pow(pow(A[0], -1, m), -e, m)
    return (U, rpow(A[1], e, d, m))


def ginv(A, d, m):
    return gpow(A, -1, d, m)


# ---- K1 -----------------------------------------------------------------
def k1():
    for q in (11, 13, 101, 103):
        s = 2
        d = s * s % q
        vals = [(a + s) * pow(a - s, -1, q) % q for a in range(q) if a not in (s % q, (-s) % q)]
        img = set(vals)
        record("K1_split", img == set(range(2, q)) and len(vals) == len(img) == q - 2
               and 1 not in img and (q - 1) in img,
               {"q": q, "image_size": len(img), "values": len(vals), "contains_minus1": (q - 1) in img})
        vals0 = [(a + s) * pow(a - s, -1, q) % q for a in range(1, q) if a not in (s % q, (-s) % q)]
        img0 = set(vals0)
        record("K1_split_a_nonzero", img0 == set(range(2, q - 1)) and len(vals0) == q - 3,
               {"q": q, "image_size": len(img0)})
    for p in (7, 11, 103, 107):
        d = next(x for x in range(2, p) if legendre(x, p) == -1)
        torus = {(x, y) for x in range(p) for y in range(p) if (x * x - d * y * y) % p == 1}
        vals = [cayley(a, d, p) for a in range(p)]
        img = set(vals)
        record("K1_inert", len(torus) == p + 1 and img == torus - {(1, 0)} and len(vals) == p,
               {"p": p, "d": d, "torus": len(torus), "image_size": len(img)})
        img0 = {cayley(a, d, p) for a in range(1, p)}
        record("K1_inert_a_nonzero", img0 == torus - {(1, 0), (p - 1, 0)},
               {"p": p, "image_size": len(img0)})


# ---- K2 -----------------------------------------------------------------
def k2():
    for r in (3, 5, 7, 11, 13):
        for a1 in range(r):
            for c in range(r):
                img = {(a1 * x - c * pow(x, -1, r)) % r for x in range(1, r)}
                if a1 and c:
                    pred = (r + legendre(-a1 * c, r)) // 2
                elif a1 or c:
                    pred = r - 1
                else:
                    pred = 1
                record("K2", len(img) == pred, {"r": r, "a1": a1, "c": c, "size": len(img), "pred": pred})


# ---- K3 -----------------------------------------------------------------
FS = {
    "x+y": lambda x, y: x + y,
    "x^2+y^2": lambda x, y: x * x + y * y,
    "x^3+y^3": lambda x, y: x ** 3 + y ** 3,
    "xy+x+y": lambda x, y: x * y + x + y,
    "x+y+(x-1)(y-1)x": lambda x, y: x + y + (x - 1) * (y - 1) * x,
}


def k3():
    for p, q in ((11, 13), (23, 47), (101, 103)):
        n = p * q
        units = [u for u in range(1, n) if math.gcd(u, n) == 1]
        for name, f in FS.items():
            ok = all(pow(u, f(p, q), n) == pow(u, f(1, n), n) for u in units)
            record("K3_G_holds", ok, {"N": n, "f": name})
        bad = sum(pow(u, 2 * p + q, n) != pow(u, 2 + n, n) for u in units)
        record("K3_G_2x+y_fails", bad > 0, {"N": n, "failing_units": bad, "units": len(units)})
        d = next(x for x in range(2, n) if jacobi(x, n) == -1)
        pi, qs = (p, q) if legendre(d, p) == -1 else (q, p)
        zs = [cayley(a, d, n) for a in range(1, 21) if math.gcd(a * a - d, n) == 1]
        ok1 = all(rpow(z, pi - qs, d, n) == rpow(z, n - 1, d, n) for z in zs)
        ok2 = all(rpow(z, (pi - qs) ** 2, d, n) == rpow(z, (n - 1) ** 2, d, n) for z in zs)
        bad = sum(rpow(z, pi + qs, d, n) != rpow(z, n + 1, d, n) for z in zs)
        record("K3_T", ok1 and ok2 and bad > 0,
               {"N": n, "d": d, "inert": pi, "zs": len(zs), "D_ok": ok1, "D2_ok": ok2, "S_fail_count": bad})


# ---- K4 -----------------------------------------------------------------
def order2pow(z, d, m):
    k, w = 0, z
    while w != (1, 0):
        w = rmul(w, w, d, m)
        k += 1
        if k > 20:
            return None
    return 1 << k


def k4():
    p, d = 8191, 3
    orders = [order2pow(cayley(a, d, p), d, p) for a in range(p)]
    small = sum(1 for o in orders if o is not None and o <= 64)
    full = sum(1 for o in orders if o == 8192)
    record("K4_orders", None not in orders and small == 63 and full == 4096,
           {"p": p, "count": len(orders), "order_le_64": small, "order_8192": full,
            "all_power_of_2": None not in orders})
    q = 257
    n = p * q
    d2 = next(x for x in range(2, n) if legendre(x, p) == -1 and legendre(x, q) == 1)
    steps = []
    for a in range(1, 31):
        if math.gcd(a * a - d2, n) != 1:
            steps.append({"a": a, "nonunit_denominator_gcd": math.gcd(a * a - d2, n)})
            continue
        z = cayley(a, d2, n)
        w, first = z, {p: None, q: None}
        split_at = None
        for k in range(0, 14):
            if k:
                w = rmul(w, w, d2, n)
            for ell in (p, q):
                if first[ell] is None and (w[0] - 1) % ell == 0 and w[1] % ell == 0:
                    first[ell] = k
            g = math.gcd(math.gcd(w[0] - 1, n), w[1])
            if split_at is None and 1 < g < n:
                split_at = k
        steps.append({"a": a, "first_k_p": first[p], "first_k_q": first[q], "split_at_k": split_at,
                      "global_one_at_13": w == (1, 0)})
    allone = all(s.get("global_one_at_13", True) for s in steps)
    record("K4_shared_annihilation", allone, {"N": n, "d": d2, "steps": steps})


# ---- K5 -----------------------------------------------------------------
def k5():
    p, q = 8191, 257
    n = p * q
    d = next(x for x in range(2, n) if legendre(x, p) == -1 and legendre(x, q) == 1)
    u, z = 3, cayley(2, d, n)
    zi = rpow(z, -1, d, n)
    U, W = 1, (1, 0)
    events = []
    ok = True
    for j in range(1, 301):
        U = U * u % n
        W = rmul(W, zi, d, n)
        g1, g2, g3 = math.gcd(U - 1, n), math.gcd(W[0] - 1, n), math.gcd(W[1], n)
        for ell in (p, q):
            one = (U - 1) % ell == 0 and (W[0] - 1) % ell == 0 and W[1] % ell == 0
            via = g1 % ell == 0 and g2 % ell == 0 and g3 % ell == 0
            ok &= one == via
        if any(1 < g < n for g in (g1, g2, g3)) or (g1 == n and g2 == n and g3 == n):
            events.append({"j": j, "gcd_u": g1, "gcd_x_minus_1": g2, "gcd_y": g3})
    record("K5", ok, {"N": n, "d": d, "events_first_12": events[:12], "event_count": len(events)})


# ---- K6, K7 setup ---------------------------------------------------------
P_TRUE, Q_TRUE = 10007, 7919
N7 = P_TRUE * Q_TRUE
D7 = next(x for x in range(2, N7) if jacobi(x, N7) == -1)
U7 = 2
Z7 = cayley(2, D7, N7)
assert math.gcd(4 - D7, N7) == 1
G7 = (U7, Z7)
HB7 = (U7, rpow(Z7, -1, D7, N7))


def k6():
    for a, b, dh in ((-1, 1, 3), (2, 5, 7), (-3, 4, 11)):
        gp = gmul(gpow(G7, b, D7, N7), gpow(HB7, a, D7, N7), D7, N7)
        lhs = gmul(gpow(gp, dh, D7, N7), gpow(HB7, -(a + b) * dh, D7, N7), D7, N7)
        rhs = (1, rpow(Z7, 2 * b * dh, D7, N7))
        record("K6", lhs == rhs, {"a": a, "b": b, "dh": dh})


def k7():
    n, d = N7, D7
    X = math.isqrt(n) + 1
    L, H, H1, B = 1200, 100, 10, 16
    a, b = -1, 1
    T = (pow(U7, n + 1, n), rpow(Z7, n - 1, d, n))
    blocks = []
    for i in range(L // H):
        Xi = X + i * H
        c0 = round(Fraction(n, Xi))
        E = math.ceil(max(abs(Fraction(b * n, Xi + h) - c0 - a * h) for h in range(H)))
        blocks.append((Xi, c0, E))
    roles = {"P_inert": (G7, HB7), "P_split": (HB7, G7)}
    pi = P_TRUE if legendre(d, P_TRUE) == -1 else Q_TRUE
    out = {"N": n, "d": d, "X": X, "inert_prime": pi, "E": [e for _, _, e in blocks], "roles": {}}
    found_roles = []
    for rname, (F, S) in roles.items():
        Fp = gmul(gpow(F, b, d, n), gpow(S, a, d, n), d, n)
        ops = 0
        table = {}
        row = (1, (1, 0))
        dup = 0
        for h1 in range(H1):
            cur = row
            for j in range(B):
                key = (cur[0], cur[1][0], cur[1][1])
                if key in table:
                    dup += 1
                table.setdefault(key, []).append((h1, j))
                cur = gmul(cur, S, d, n)
                ops += 1
            row = gmul(row, Fp, d, n)
            ops += 1
        babies = H1 * B
        giants = matches = tests = 0
        found = None
        Fstep = gpow(Fp, -H1, d, n)
        Sstep = gpow(S, -B, d, n)
        pred = 0
        for Xi, c0, E in blocks:
            tgt = gmul(gmul(gpow(T, b, d, n), gpow(F, -b * Xi, d, n), d, n), gpow(S, -c0, d, n), d, n)
            nk = -(-(2 * E + 1) // B)
            pred += -(-H // H1) * nk
            base_h = gmul(tgt, gpow(S, E, d, n), d, n)
            for h2 in range(-(-H // H1)):
                g = base_h
                for k in range(nk):
                    giants += 1
                    for h1, j in table.get((g[0], g[1][0], g[1][1]), []):
                        matches += 1
                        h = h1 + H1 * h2
                        e = j + k * B - E
                        if h < H and abs(e) <= E:
                            tests += 1
                            P = Xi + h
                            if n % P == 0:
                                found = P
                    g = gmul(g, Sstep, d, n)
                    ops += 1
                base_h = gmul(base_h, Fstep, d, n)
                ops += 1
        # literal 1-D schedule on the same blocks
        B1 = max(2 * E + 1 for _, _, E in blocks)
        t1 = {}
        cur = (1, (1, 0))
        for j in range(B1):
            t1[(cur[0], cur[1][0], cur[1][1])] = j
            cur = gmul(cur, S, d, n)
        g1count, found1 = 0, None
        Finv = ginv(Fp, d, n)
        for Xi, c0, E in blocks:
            tgt = gmul(gmul(gpow(T, b, d, n), gpow(F, -b * Xi, d, n), d, n), gpow(S, -c0 + E, d, n), d, n)
            g = tgt
            for h in range(H):
                g1count += 1
                j = t1.get((g[0], g[1][0], g[1][1]))
                if j is not None and n % (Xi + h) == 0:
                    found1 = Xi + h
                g = gmul(g, Finv, d, n)
        out["roles"][rname] = {"babies": babies, "giants": giants, "pred_giants": pred,
                               "dup_baby_keys": dup, "matches": matches, "div_tests": tests,
                               "found": found, "loop_group_ops": ops,
                               "literal1D": {"B1": B1, "giants": g1count, "found": found1}}
        if found:
            found_roles.append(rname)
        record("K7_counts", giants == pred and dup == 0 and g1count == L,
               {"role": rname, "giants": giants, "pred": pred, "dup": dup, "literal_giants": g1count})
    record("K7_found_once", found_roles and len(found_roles) == 1 and
           out["roles"][found_roles[0]]["found"] == P_TRUE and
           out["roles"][found_roles[0]]["literal1D"]["found"] == P_TRUE,
           {"found_roles": found_roles})
    RESULTS["K7"] = out


for fn in (k1, k2, k3, k4, k5, k6, k7):
    try:
        fn()
    except Exception as exc:  # retained, not hidden
        record(fn.__name__ + "_exception", False, {"error": repr(exc)})

summary = {name: {"total": len(v), "passed": sum(x["ok"] for x in v)} for name, v in RESULTS["checks"].items()}
RESULTS["summary"] = summary
# keep K2 output compact: only failures are listed individually
RESULTS["checks"]["K2"] = [x for x in RESULTS["checks"].get("K2", []) if not x["ok"]]
json.dump(RESULTS, sys.stdout, indent=1, sort_keys=True)
sys.exit(1 if RESULTS["failures"] else 0)
