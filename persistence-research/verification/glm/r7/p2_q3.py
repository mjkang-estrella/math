# r7 p2_q3.py — the q=3 slice of (M*) for S_low=1 (K=8, t0=3): here t = v2(10^L+A*10^3+8)
# is NOT t0 in general, so the pair sieve (which pins t = t0, valid only for q > t0)
# excludes q=3. Piecewise, t is still explicit:
#   10^L + A*10^3 + 8 = 2^3 * (2^{L-3} 5^L + 125 A + 1)   (L >= 4)
#   A=9 : t = 6 for L=4;           t = 4 for L >= 5   (since 2^{L-3}5^L+1126 ≡ 2 mod 8)
#   A=18: t = 3 for all L >= 4                       (bracket odd)
#   A=27: t = 4,5,6,16 for L=4..7; t = 7 for L >= 8   (2^{L-3}5^L ≡ 0 mod 256)
# So each A reduces to finitely many direct L plus a 1-D sieve "10^L + Kp = 2^tp 3^a 7^w"
# with t = tp pinned on L >= Lmin (same kill machinery as Part 1: T0, region, size).
# Run: bash -c 'ulimit -v 3000000; python3 -I p2_q3.py'

import math, sys

MAXM = int(__import__('os').environ.get('P2MAXM', '100000000'))
CLASS_CAP = 3_000_000
KILL_SCAN = 500
ALIGN_CAP = 4096

def vp(n, p):
    c = 0
    while n % p == 0:
        n //= p; c += 1
    return c

def smooth237(x):
    for p in (2, 3, 7):
        while x % p == 0:
            x //= p
    return x == 1

def primes_upto(b):
    s = [True] * b
    for i in range(2, int(b ** 0.5) + 1):
        if s[i]:
            for j in range(i * i, b, i): s[j] = False
    return [i for i in range(2, b) if s[i]]

def ord_of(a, q):
    d = q - 1; n = d; f = 2
    while f * f <= n:
        if n % f == 0:
            while n % f == 0: n //= f
            while d % f == 0 and pow(a, d // f, q) == 1: d //= f
        f += 1
    if n > 1:
        while d % n == 0 and pow(a, d // n, q) == 1: d //= n
    return d

def ord_pp(a, p, k):
    if k <= 0: return 1
    o = 1; x = a % p
    while x != 1:
        x = x * a % p; o += 1
    cur = p
    while cur < p ** k:
        cur *= p
        if pow(a, o, cur) != 1: o *= p
    return o

ALLP = [q for q in primes_upto(50000) if q not in (2, 3, 5, 7)]
ORD10 = {}; O3 = {}; O7 = {}
for q in ALLP:
    ORD10[q] = ord_of(10, q); O3[q] = ord_of(3, q); O7[q] = ord_of(7, q)
PORDER = sorted(ALLP, key=lambda q: (O3[q] * O7[q] // math.gcd(O3[q], O7[q])) / (q - 1))

def could(T, m, sig, o3, o7):
    if T == 0: return False
    (a_lo, a_hi), (w_lo, w_hi) = sig
    x = T * pow(pow(3, a_lo, m), -1, m) % m
    x = x * pow(pow(7, w_lo, m), -1, m) % m
    if a_hi is None and w_hi is None:
        return pow(x, o3 * o7 // math.gcd(o3, o7), m) == 1
    if a_hi is None: return pow(x, o3, m) == 1
    if w_hi is None: return pow(x, o7, m) == 1
    return x == 1

def signature(Kp, rho, M):
    j = vp(M, 3); m3 = 3 ** (j + 2)
    X = (pow(10, rho, m3) + Kp) % m3
    e3 = vp(X, 3) if X else j + 2
    a = (e3, e3) if e3 <= j + 1 else (j + 2, None)
    i = vp(M, 7); m7 = 7 ** (i + 1)
    Y = (pow(10, rho, m7) + Kp) % m7
    e7 = vp(Y, 7) if Y else i + 1
    w = (e7, e7) if e7 <= i else (i + 1, None)
    return a, w

def sieve1d(Kp, tp, Lmin, brute):
    """Kill all classes {rho mod M}, M >= 6, for 10^L + Kp = 2^tp 3^a 7^w, L >= Lmin."""
    inv2 = {q: pow(pow(2, tp, q), -1, q) for q in ALLP}
    stack = list(range(6))
    seen = set(); nc = 0; reasons = {}; recorded = []
    while stack:
        rho = stack.pop()
        M = 6  # placeholder; store (rho, M) pairs instead
        # -- reworked below --
    return None

def sieve1d2(Kp, tp, Lmin, brute):
    inv2 = {q: pow(pow(2, tp, q), -1, q) for q in ALLP}
    stack = [(r, 6) for r in range(6)]
    seen = set(); nc = 0; reasons = {}; recorded = []
    def check_no_sol(rho, M, tag):
        for (L,) in brute:
            if L >= Lmin and L % M == rho % M:
                raise AssertionError(f"FALSE KILL [{tag}] class {rho} mod {M} contains L={L}")
    while stack:
        rho, M = stack.pop()
        if (rho, M) in seen: continue
        seen.add((rho, M))
        nc += 1
        if nc > CLASS_CAP:
            return dict(status="CAP", nc=nc, recorded=recorded, reasons=reasons)
        sig = signature(Kp, rho, M)
        (a_lo, a_hi), (w_lo, w_hi) = sig
        if a_hi is not None and w_hi is not None:
            N0 = 2 ** tp * 3 ** a_lo * 7 ** w_lo
            if N0 > Kp:
                r = N0 - Kp; e = vp(r, 10) if r > 0 else -1
                rr = r
                while rr % 10 == 0: rr //= 10
                if rr == 1 and r > 0:
                    L = e
                    if L >= Lmin and L % M == rho % M and 10 ** L + Kp == N0:
                        recorded.append(L)
            reasons["size"] = reasons.get("size", 0) + 1
            continue
        # T0
        killed = None
        for p in PORDER[:KILL_SCAN]:
            d = ORD10[p]
            if M % d == 0 and (pow(10, rho, p) + Kp) % p == 0:
                killed = ("T0", p); break
        # region
        if not killed:
            for p in PORDER[:KILL_SCAN]:
                d = ORD10[p]; g = math.gcd(M, d)
                if d // g > ALIGN_CAP: continue
                alive = False
                for gg in range(rho % g, d, g):
                    T = (pow(10, gg, p) + Kp) * inv2[p] % p
                    if could(T, p, sig, O3[p], O7[p]):
                        alive = True; break
                if not alive:
                    killed = ("prime", p); break
        # pin mod 5^3 (q = 3 fixed): 3^a 7^w ≡ Kp 2^{-tp} (mod 125)
        if not killed:
            m = 125
            x0 = Kp * pow(pow(2, tp, m), -1, m) % m
            if not could(x0, m, sig, ord_pp(3, 5, 3), ord_pp(7, 5, 3)):
                killed = ("pin", "5^3")
        if killed:
            check_no_sol(rho, M, killed[0])
            reasons[killed[0]] = reasons.get(killed[0], 0) + 1
            continue
        # no kill: deepen x3 or x7 (pick side with unbounded/needs-exact signature)
        ua = a_hi is None; uw = w_hi is None
        mult = 3 if (ua and (not uw or vp(M,3) <= vp(M,7))) else 7
        nM = M * mult
        if nM > MAXM:
            return dict(status="RESIDUAL", cls=(rho, M), nc=nc, recorded=recorded, reasons=reasons)
        for s in range(mult):
            stack.append(((rho + s * M) % nM, nM))
    return dict(status="CLOSED", nc=nc, recorded=sorted(set(recorded)), reasons=reasons)

# t-claim verification and execution
CASES = [
    (9,  [4],        5, 9 * 1000 + 8, 4),
    (18, [],         4, 18 * 1000 + 8, 3),
    (27, [4, 5, 6, 7], 8, 27 * 1000 + 8, 7),
]
for A, direct, Lmin, Kp, tp in CASES:
    # verify the pinned t on a wide range
    for L in range(Lmin, 150):
        assert vp(10 ** L + Kp, 2) == tp, f"A={A}: t claim fails at L={L}"
    # direct small L
    drec = []
    for L in direct:
        X = 10 ** L + Kp
        if smooth237(X):
            drec.append((L, X // 9, vp(X,2), vp(X,3), vp(X,7)))
    brute = [(L, 3) for L in range(4, 600) if smooth237(10 ** L + A * 1000 + 8)]
    brute_in = [(L,) for (L, q) in brute if L >= Lmin]
    res = sieve1d2(Kp, tp, Lmin, brute_in)
    print(f"A={A}: direct={drec} sieve={res['status']} nc={res['nc']} "
          f"recorded={res['recorded']} reasons={res['reasons']} brute(L>={Lmin})={brute_in}",
          flush=True)
