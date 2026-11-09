# r7 p2_sieve.py — two-variable sieve for the mixed residual (M*):
#   2^t 3^a 7^w = 10^L + A*10^q + K,  L > q >= 3,  K = 9*S_low - 1,  t = t0 = v2(K).
# t = t0 is valid iff q > t0; hence for S_low=1 (t0=3) the pair sieve runs on q >= 4
# and q = 3 is handled separately in p2_q3.py (piecewise-exact t).
#
# Class = (rho mod ML, kappa mod MQ).  j = min(v3(ML), v3(MQ)),
# i = min(v7(ML), v7(MQ)); signature a from (10^rho + A*10^kappa + K) mod 3^{j+2},
# w from ... mod 7^{i+1} (uniform because ord_{3^{j+2}}(10) = 3^j and
# ord_{7^{i+1}}(10) = 6*7^i divide both ML and MQ).
# Kills: T0 (p | RHS on the whole class), aux-prime region tests over all aligned
# (L mod d, q mod d) combos, size resolution when a,w both exact
# (10^q (10^{L-q} + A) = N0 - K), and the pin 3^a 7^w ≡ K 2^{-t0} mod 2^{qmin}/5^{qmin}.
# Run: bash -c 'ulimit -v 3000000; python3 -I p2_sieve.py [S A]  (or all)'

import math, sys

MAXM = int(__import__('os').environ.get('P2MAXM', '100000000'))
CLASS_CAP = 3_000_000
KILL_SCAN = 400
COMBO_CAP = 64          # max (d/gL)*(d/gQ) for whole-class region kill attempts
SPLIT_SCAN = 50
SPLIT_CAP = 256         # max children for a prime split
QMIN_CAP = 40           # max qmin for pin kills (2^qmin must be computable)

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
    # order of a mod prime q via factoring q-1 (q must be prime)
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
    # order of a mod p^k via lifting (p prime, a coprime to p)
    if k == 0: return 1
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

class Ctx:
    def __init__(self, S, A):
        self.S = S; self.A = A
        self.K = 9 * S - 1
        self.t0 = vp(self.K, 2)
        self.qlo = max(3, self.t0 + 1)

def signature(ctx, rho, ML, kappa, MQ):
    K, A = ctx.K, ctx.A
    j = min(vp(ML, 3), vp(MQ, 3)); m3 = 3 ** (j + 2)
    X = (pow(10, rho, m3) + A * pow(10, kappa, m3) + K) % m3
    e3 = vp(X, 3) if X else j + 2
    a = (e3, e3) if e3 <= j + 1 else (j + 2, None)
    i = min(vp(ML, 7), vp(MQ, 7)); m7 = 7 ** (i + 1)
    Y = (pow(10, rho, m7) + A * pow(10, kappa, m7) + K) % m7
    e7 = vp(Y, 7) if Y else i + 1
    w = (e7, e7) if e7 <= i else (i + 1, None)
    return a, w

def could(T, m, sig, o3, o7):
    """T ≡ 3^a 7^w (mod m) possible for a,w in ranges?  (m any modulus coprime to 3,7)"""
    if T == 0: return False
    (a_lo, a_hi), (w_lo, w_hi) = sig
    x = T * pow(pow(3, a_lo, m), -1, m) % m
    x = x * pow(pow(7, w_lo, m), -1, m) % m
    if a_hi is None and w_hi is None:
        return pow(x, o3 * o7 // math.gcd(o3, o7), m) == 1
    if a_hi is None: return pow(x, o3, m) == 1
    if w_hi is None: return pow(x, o7, m) == 1
    return x == 1

def q_minimum(kappa, MQ, qlo):
    q = kappa % MQ
    while q < qlo: q += MQ
    return q

def size_solutions(ctx, rho, ML, kappa, MQ, a0, w0):
    """All (L,q) in the class with 10^L + A 10^q + K = 2^t0 3^a0 7^w0 exactly."""
    N0 = 2 ** ctx.t0 * 3 ** a0 * 7 ** w0
    R = N0 - ctx.K
    out = []
    if R > 0:
        q = 0; p10 = 1
        while p10 <= R:
            if R % p10 == 0:
                u = R // p10 - ctx.A
                if u > 0:
                    e = vp(u, 10)
                    if 10 ** e == u:
                        L = q + e
                        if e >= 1 and q >= ctx.qlo and L % ML == rho % ML and q % MQ == kappa % MQ:
                            if 10 ** L + ctx.A * 10 ** q + ctx.K == N0:
                                out.append((L, q))
            q += 1; p10 *= 10
    return out

def try_kill(ctx, rho, ML, kappa, MQ, sig):
    K, A, t0, qlo = ctx.K, ctx.A, ctx.t0, ctx.qlo
    inv2 = pow(pow(2, t0, 3), -1, 3)  # placeholder, per-prime below
    # 1. T0
    for p in PORDER[:KILL_SCAN]:
        d = ORD10[p]
        if ML % d == 0 and MQ % d == 0 and (pow(10, rho, p) + A * pow(10, kappa, p) + K) % p == 0:
            return ("T0", p)
    # 2. region tests
    for p in PORDER[:KILL_SCAN]:
        d = ORD10[p]
        gL = math.gcd(ML, d); gQ = math.gcd(MQ, d)
        nL, nQ = d // gL, d // gQ
        if nL * nQ > COMBO_CAP or nL * nQ < 2:
            continue
        inv2t0 = pow(pow(2, t0, p), -1, p)
        o3, o7 = O3[p], O7[p]
        alive = False
        for LL in range(rho % gL, d, gL):
            pLL = pow(10, LL, p)
            for QQ in range(kappa % gQ, d, gQ):
                T = (pLL + A * pow(10, QQ, p) + K) * inv2t0 % p
                if could(T, p, sig, o3, o7):
                    alive = True; break
            if alive: break
        if not alive:
            return ("prime", p)
    # 3. pin kills mod 2^qmin and 5^qmin
    qmin = q_minimum(kappa, MQ, qlo)
    # pin: 2^t0 3^a 7^w ≡ K (mod 10^{q}) for the true q >= qmin; hence the pin
    # holds mod 10^{q'} for EVERY q' <= qmin — use q' = min(qmin, QMIN_CAP).
    qe = min(qmin, QMIN_CAP)
    if qe - t0 >= 1 or True:
        for base, e in ((2, qe - t0), (5, qe)):
            if e < 1: continue
            m = base ** e
            x0 = (K // 2 ** t0) % m if base == 2 else \
                 K * pow(pow(2, t0, m), -1, m) % m
            o3, o7 = ord_pp(3, base, e), ord_pp(7, base, e)
            if not could(x0, m, sig, o3, o7):
                return ("pin", f"{base}^{qe}")
    return None

def best_split(ctx, rho, ML, kappa, MQ):
    best = None
    for p in PORDER[:SPLIT_SCAN]:
        d = ORD10[p]
        gL = math.gcd(ML, d); gQ = math.gcd(MQ, d)
        nL, nQ = d // gL, d // gQ
        nc = nL * nQ
        if nc < 2 or nc > SPLIT_CAP or max(ML * nL, MQ * nQ) > MAXM:
            continue
        killed = 0
        for s in range(nL):
            cL = (rho + s * ML) % (ML * nL)
            for t in range(nQ):
                cQ = (kappa + t * MQ) % (MQ * nQ)
                sg = signature(ctx, cL, ML * nL, cQ, MQ * nQ)
                T = (pow(10, cL, p) + ctx.A * pow(10, cQ, p) + ctx.K) * pow(pow(2, ctx.t0, p), -1, p) % p
                if not could(T, p, sg, O3[p], O7[p]):
                    killed += 1
        if killed == 0: continue
        surv = nc - killed
        key = (surv, -killed)
        if best is None or key < best[0]:
            best = (key, p, nL, nQ)
    return best

class CtxK:
    """Generic spec: equation 2^t 3^a 7^w = 10^L + A*10^q + K, t = t0 for q >= qlo."""
    def __init__(self, K, A, t0, qlo):
        self.K = K; self.A = A; self.t0 = t0; self.qlo = qlo

def sieve(ctx, brute=(), verbose=True):
    K, A, t0, qlo = ctx.K, ctx.A, ctx.t0, ctx.qlo
    bruteS = set(brute)
    def check_no_sol(rho, ML, kappa, MQ, tag):
        for (L, q) in bruteS:
            if q >= qlo and L % ML == rho % ML and q % MQ == kappa % MQ:
                raise AssertionError(f"FALSE KILL [{tag}] class ({rho},{ML},{kappa},{MQ}) "
                                     f"contains brute solution (L={L},q={q})")
    # class: (rho, ML, kappa, MQ)
    stack = [(r, 6, k, 6) for r in range(6) for k in range(6)]
    seen = set()
    recorded = []
    residual = []
    nc = 0
    reasons = {}
    while stack:
        rho, ML, kappa, MQ = stack.pop()
        key = (rho, ML, kappa, MQ)
        if key in seen: continue
        seen.add(key)
        nc += 1
        if nc > CLASS_CAP:
            return dict(status="CAP", nc=nc, residual=len(stack) + 1, recorded=recorded)
        if nc % 20000 == 0:
            print(f"  ..nc={nc} stack={len(stack)} Mmax={max(ML,MQ)}", flush=True)
        sig = signature(ctx, rho, ML, kappa, MQ)
        (a_lo, a_hi), (w_lo, w_hi) = sig
        if a_hi is not None and w_hi is not None:
            rec = size_solutions(ctx, rho, ML, kappa, MQ, a_lo, w_lo)
            for s in rec:
                assert s in bruteS, f"recorded {s} not in brute list"
            recorded += rec
            reasons["size"] = reasons.get("size", 0) + 1
            continue
        kill = try_kill(ctx, rho, ML, kappa, MQ, sig)
        if kill:
            check_no_sol(rho, ML, kappa, MQ, kill[0])
            reasons[kill[0]] = reasons.get(kill[0], 0) + 1
            continue
        bs = best_split(ctx, rho, ML, kappa, MQ)
        use = False
        if bs is not None:
            (surv, _k), p, nL, nQ = bs
            if surv <= 6 or surv <= 0.25 * nL * nQ:
                use = True
        if use:
            (_, p, nL, nQ) = bs
            nML, nMQ = ML * nL, MQ * nQ
            for s in range(nL):
                cL = (rho + s * ML) % nML
                for t in range(nQ):
                    cQ = (kappa + t * MQ) % nMQ
                    sg = signature(ctx, cL, nML, cQ, nMQ)
                    T = (pow(10, cL, p) + A * pow(10, cQ, p) + K) * pow(pow(2, t0, p), -1, p) % p
                    if could(T, p, sg, O3[p], O7[p]):
                        stack.append((cL, nML, cQ, nMQ))
            continue
        # deepen: raise min 3- or 7-valuation, one coordinate at a time (3 or 7 children)
        ja = min(vp(ML, 3), vp(MQ, 3)); ia = min(vp(ML, 7), vp(MQ, 7))
        ua = a_hi is None; uw = w_hi is None
        if ua and (not uw or ja <= ia):
            if vp(ML, 3) <= vp(MQ, 3): mult, which = 3, "L"
            else: mult, which = 3, "Q"
        elif uw:
            if vp(ML, 7) <= vp(MQ, 7): mult, which = 7, "L"
            else: mult, which = 7, "Q"
        else:
            mult, which = 3, "L"
        if which == "L":
            nML = ML * mult
            if nML > MAXM:
                residual.append(key); continue
            for s in range(mult):
                stack.append(((rho + s * ML) % nML, nML, kappa, MQ))
        else:
            nMQ = MQ * mult
            if nMQ > MAXM:
                residual.append(key); continue
            for s in range(mult):
                stack.append((rho, ML, (kappa + s * MQ) % nMQ, nMQ))
    return dict(status="CLOSED", nc=nc, recorded=sorted(set(recorded)), reasons=reasons,
                residual=residual)

PAIRS = [(1, 9), (10, 9), (1, 18), (10, 18), (1, 27), (10, 27),
         (30, 27), (11, 9), (101, 9), (110, 9)]

def brute_pair(S, A, LMAX=600):
    K = 9 * S - 1
    p10 = [10 ** i for i in range(LMAX + 2)]
    out = []
    for L in range(4, LMAX + 1):
        base = p10[L] + K
        for q in range(3, L):
            if smooth237(base + A * p10[q]):
                out.append((L, q))
    return out

if __name__ == "__main__":
    args = sys.argv[1:]
    todo = PAIRS
    if len(args) == 2:
        todo = [(int(args[0]), int(args[1]))]
    for S, A in todo:
        ctx = Ctx(S, A)
        br = brute_pair(S, A)
        res = sieve(ctx, brute=br)
        print(f"S_low={S:>3} A={A:>2} K={ctx.K:>4} t0={ctx.t0} qlo={ctx.qlo}: "
              f"{res['status']} classes={res['nc']} recorded={res['recorded']} reasons={res.get('reasons')} "
              f"brute(q>=qlo,L<=600)={[(L,q) for L,q in br]}",
              flush=True)
