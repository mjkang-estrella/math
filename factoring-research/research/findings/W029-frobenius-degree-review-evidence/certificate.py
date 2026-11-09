"""W029 review certificate: one frozen run, fixed inputs, no sweeps.

Checks (all rows retained, failures recorded, never aborts early):
 C1 integer identity F_r' = -2 r G_(r-1), r = 2..12 (exact coefficients over Z).
 C2 exact degrees mod p / mod q and leading-index gcd for N in {15, 21, 35}.
 C3 identity H_N(x) = -2 G_(N-1)(x) == (F_N(x) - G_N(x)) / (2x) mod N, all units x, N in {35, 91}.
 C4 per-prime zero count of G_(N-1) over F_p versus Z = (g+ + g-)/2 - 2,
    g+ = gcd(p-1,q-1), g- = gcd(p+1,q+1), for fixed pairs listed in PAIRS.
 C5 full split count of gcd(H_N(x), N) over x in Z/N for N in {21, 35}.
Budget: 20000 charged events, 60 s wall clock.
"""
import json, math, sys, time

BUDGET = 20000
DEADLINE = 60.0
PAIRS = [(3, 7), (5, 7), (7, 13), (11, 31), (13, 29)]
ev = 0
t0 = time.monotonic()

def charge(k=1):
    global ev
    ev += k
    if ev > BUDGET or time.monotonic() - t0 > DEADLINE:
        raise RuntimeError("budget")

def pair_pow(x, r, m):
    """(F_r(x), G_r(x)) mod m by binary powering of (1,1); A = 1-4x."""
    A = (1 - 4 * x) % m
    F, G = 1, 0
    bF, bG = 1, 1
    while r:
        if r & 1:
            charge(); F, G = (F * bF + A * G * bG) % m, (F * bG + G * bF) % m
        r >>= 1
        if r:
            charge(); bF, bG = (bF * bF + A * bG * bG) % m, (2 * bF * bG) % m
    return F, G

def poly_FG(r):
    """Exact integer coefficient lists of F_r, G_r (index = power of X)."""
    F = [0] * (r // 2 + 1); G = [0] * ((r - 1) // 2 + 1 if r >= 1 else 1)
    for j in range(r // 2 + 1):
        c = math.comb(r, 2 * j)
        for k in range(j + 1):
            charge(); F[k] += c * math.comb(j, k) * (-4) ** k
    for j in range((r - 1) // 2 + 1):
        c = math.comb(r, 2 * j + 1)
        for k in range(j + 1):
            charge(); G[k] += c * math.comb(j, k) * (-4) ** k
    return F, G

out = {"C1": [], "C2": [], "C3": [], "C4": [], "C5": [], "status": "ok"}
try:
    for r in range(2, 13):
        F, _ = poly_FG(r); _, G1 = poly_FG(r - 1)
        dF = [k * F[k] for k in range(1, len(F))]
        rhs = [-2 * r * c for c in G1]
        L = max(len(dF), len(rhs)); dF += [0] * (L - len(dF)); rhs += [0] * (L - len(rhs))
        out["C1"].append({"r": r, "ok": dF == rhs})
    for (p, q) in [(3, 5), (3, 7), (5, 7)]:
        N = p * q
        F, _ = poly_FG(N)
        dp = max(k for k, c in enumerate(F) if c % p)
        dq = max(k for k, c in enumerate(F) if c % q)
        dN = max(k for k, c in enumerate(F) if c % N)
        out["C2"].append({"N": N, "deg_mod_p": dp, "pred_p": (N - p) // 2,
                          "deg_mod_q": dq, "pred_q": (N - q) // 2,
                          "top_index_modN": dN, "N_minus_2r": N - 2 * dN,
                          "gcd_top_coeff_N": math.gcd(F[dN], N),
                          "lead_mod_p_ok": F[dp] % p == (q * (-4) ** ((q - 1) // 2)) % p})
    for N in (35, 91):
        bad = 0; units = 0
        for x in range(N):
            if math.gcd(x, N) != 1:
                continue
            units += 1
            _, G1 = pair_pow(x, N - 1, N); FN, GN = pair_pow(x, N, N)
            if (-2 * G1 - (FN - GN) * pow(2 * x, -1, N)) % N:
                bad += 1
        out["C3"].append({"N": N, "units": units, "mismatches": bad})
    for (p, q) in PAIRS:
        N = p * q
        gp, gm = math.gcd(p - 1, q - 1), math.gcd(p + 1, q + 1)
        Z = (gp + gm) // 2 - 2
        row = {"p": p, "q": q, "g_plus": gp, "g_minus": gm, "Z_pred": Z}
        for name, ell in (("p", p), ("q", q)):
            zs = [x for x in range(ell) if pair_pow(x, N - 1, ell)[1] % ell == 0]
            row["zeros_mod_" + name] = zs
            row["count_mod_" + name] = len(zs)
        row["ok"] = row["count_mod_p"] == Z and row["count_mod_q"] == Z
        out["C4"].append(row)
    for N in (21, 35):
        hist = {}
        for x in range(N):
            _, G1 = pair_pow(x, N - 1, N)
            g = math.gcd((-2 * G1) % N, N)
            hist[g] = hist.get(g, 0) + 1
        out["C5"].append({"N": N, "gcd_histogram_over_all_x": {str(k): v for k, v in sorted(hist.items())}})
except RuntimeError as e:
    out["status"] = "stopped:" + str(e)
out["events"] = ev
out["seconds"] = time.monotonic() - t0
json.dump(out, sys.stdout, indent=1)
