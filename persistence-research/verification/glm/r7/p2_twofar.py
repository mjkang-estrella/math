# r7 p2_twofar.py — the {2,2,2} two-far-digit case:
#   2^t 3^a 7^w = 10^L + 9*10^q1 + 9*10^q2 + K,  K = 9*S_low - 1,  S_low in {1, 10},
#   3 <= q1 < q2 < L.
# t-pin analysis (RHS = 2^{q1} B + K with B even):
#   S=10 (t0=0): t = 0 for all q1 >= 1                    -> 3-D sieve, qlo=3
#   S=1  (t0=3): RHS = 2^3(2^{q1-3}B + 1), bracket odd for q1 >= 4
#                => t = 3 for q1 >= 4                     -> 3-D sieve, qlo=4
#                q1 = 3: t = 3 + v2(2^{L-3}5^L + 1126 + 9*2^{q2-3}5^{q2}):
#                  (L,q2)=(5,4): t=5; (6,4): t=8   -> direct checks
#                  q2=4, L>=7:  t=6 pinned         -> 1-D sieve, K=10^L-part 99008
#                  q2>=5:      t=4 pinned (L>=6)   -> 2-D sieve, K=9008, qlo=5
# 3-D kills: T0, aux-prime region tests over aligned triples, pin
# 2^t 3^a 7^w ≡ K (mod 10^{qmin}) (10^L, 9*10^q1, 9*10^q2 all vanish mod 10^{q1}),
# exact-size resolution via N0 - K = 10^{q1}(10^{L-q1} + 9 + 9*10^{q2-q1}).
# Run: bash -c 'ulimit -v 3000000; python3 -I p2_twofar.py'

import math, sys, os

MAXM = int(os.environ.get('P2MAXM', '100000000'))
CLASS_CAP = 3_000_000
KILL_SCAN = 300
COMBO_CAP = 64          # (d/g)^3 combos for whole-class region kills
SPLIT_CAP = 64
QMIN_CAP = 36
LCHECK = 250            # brute-force cross-check range

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

def is_power10(x):
    if x <= 0: return None
    e = 0
    while x % 10 == 0:
        x //= 10; e += 1
    return e if x == 1 else None

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

def signature3(K, rhoL, rho1, rho2, M):
    j = vp(M, 3); m3 = 3 ** (j + 2)
    X = (pow(10, rhoL, m3) + 9 * pow(10, rho1, m3) + 9 * pow(10, rho2, m3) + K) % m3
    e3 = vp(X, 3) if X else j + 2
    a = (e3, e3) if e3 <= j + 1 else (j + 2, None)
    i = vp(M, 7); m7 = 7 ** (i + 1)
    Y = (pow(10, rhoL, m7) + 9 * pow(10, rho1, m7) + 9 * pow(10, rho2, m7) + K) % m7
    e7 = vp(Y, 7) if Y else i + 1
    w = (e7, e7) if e7 <= i else (i + 1, None)
    return a, w

def q_minimum(rho1, M, qlo):
    q = rho1 % M
    while q < qlo: q += M
    return q

def size_solutions3(K, t0, rhoL, rho1, rho2, M, a0, w0, qlo):
    N0 = 2 ** t0 * 3 ** a0 * 7 ** w0
    R = N0 - K
    out = []
    if R > 0:
        q1 = 0; p10 = 1
        while p10 <= R:
            if R % p10 == 0:
                u = R // p10 - 9
                if u > 9:
                    s = 1; f = 10
                    while 9 * f < u:
                        v = u - 9 * f
                        e = is_power10(v)
                        if e is not None and e >= 1:
                            L = q1 + e; q2 = q1 + s
                            if L > q2 and q1 >= qlo and q2 > q1 \
                               and L % M == rhoL % M and q1 % M == rho1 % M and q2 % M == rho2 % M:
                                if 10 ** L + 9 * 10 ** q1 + 9 * 10 ** q2 + K == N0:
                                    out.append((L, q1, q2))
                        s += 1; f *= 10
            q1 += 1; p10 *= 10
    return out

def try_kill3(K, t0, qlo, rhoL, rho1, rho2, M, sig):
    for p in PORDER[:KILL_SCAN]:
        d = ORD10[p]
        if M % d == 0 and (pow(10, rhoL, p) + 9 * pow(10, rho1, p) +
                           9 * pow(10, rho2, p) + K) % p == 0:
            return ("T0", p)
    for p in PORDER[:KILL_SCAN]:
        d = ORD10[p]; g = math.gcd(M, d); n = d // g
        if n ** 3 > COMBO_CAP or n < 2: continue
        inv2t0 = pow(pow(2, t0, p), -1, p)
        o3, o7 = O3[p], O7[p]
        alive = False
        for LL in range(rhoL % g, d, g):
            pL = pow(10, LL, p)
            for Q1 in range(rho1 % g, d, g):
                p1 = 9 * pow(10, Q1, p)
                for Q2 in range(rho2 % g, d, g):
                    T = (pL + p1 + 9 * pow(10, Q2, p) + K) * inv2t0 % p
                    if could(T, p, sig, o3, o7):
                        alive = True; break
                if alive: break
            if alive: break
        if not alive:
            return ("prime", p)
    qmin = q_minimum(rho1, M, qlo)
    # pin holds mod 10^{q'} for every q' <= qmin; use q' = min(qmin, QMIN_CAP)
    qe = min(qmin, QMIN_CAP)
    for base, e in ((2, qe - t0), (5, qe)):
        if e < 1: continue
        m = base ** e
        x0 = (K // 2 ** t0) % m if base == 2 else \
             K * pow(pow(2, t0, m), -1, m) % m
        o3 = ord_pp(3, base, e); o7 = ord_pp(7, base, e)
        if not could(x0, m, sig, o3, o7):
            return ("pin", f"{base}^{qe}")
    return None

def best_split3(K, t0, rhoL, rho1, rho2, M):
    best = None
    for p in PORDER[:200]:
        d = ORD10[p]
        g = math.gcd(M, d); n = d // g
        if n < 2 or n ** 3 > SPLIT_CAP or M * n > MAXM:
            continue
        nM = M * n
        killed = 0; total = 0
        for sL in range(n):
            cL = (rhoL + sL * M) % nM
            for s1 in range(n):
                c1 = (rho1 + s1 * M) % nM
                for s2 in range(n):
                    c2 = (rho2 + s2 * M) % nM
                    total += 1
                    sg = signature3(K, cL, c1, c2, nM)
                    Tv = (pow(10, cL, p) + 9 * pow(10, c1, p) + 9 * pow(10, c2, p) + K) * pow(pow(2, t0, p), -1, p) % p
                    if not could(Tv, p, sg, O3[p], O7[p]):
                        killed += 1
        if killed == 0: continue
        surv = total - killed
        key = (surv, -killed)
        if best is None or key < best[0]:
            best = (key, p, n)
    return best

def sieve3d(K, t0, qlo, brute):
    bruteS = set(brute)
    stack = [(rL, r1, r2, 6, 0) for rL in range(6) for r1 in range(6) for r2 in range(6)]
    seen = set(); nc = 0; reasons = {}; recorded = []; residual = []
    def check_no_sol(key, tag):
        rhoL, rho1, rho2, M, _ph = key
        for (L, q1, q2) in bruteS:
            if q1 >= qlo and L % M == rhoL % M and q1 % M == rho1 % M and q2 % M == rho2 % M:
                raise AssertionError(f"FALSE KILL [{tag}] {key} contains {(L,q1,q2)}")
    while stack:
        key = stack.pop()
        if key in seen: continue
        seen.add(key)
        nc += 1
        if nc % 200000 == 0:
            print(f"   ..nc={nc} stack={len(stack)} Mmax={key[3]}", flush=True)
        if nc > CLASS_CAP:
            return dict(status="CAP", nc=nc, recorded=recorded, residual=stack)
        rhoL, rho1, rho2, M, ph = key
        sig = signature3(K, rhoL, rho1, rho2, M)
        (a_lo, a_hi), (w_lo, w_hi) = sig
        if a_hi is not None and w_hi is not None:
            rec = size_solutions3(K, t0, rhoL, rho1, rho2, M, a_lo, w_lo, qlo)
            for s in rec:
                assert s in bruteS, f"recorded {s} not in brute list"
            recorded += rec
            reasons["size"] = reasons.get("size", 0) + 1
            continue
        kill = try_kill3(K, t0, qlo, rhoL, rho1, rho2, M, sig)
        if kill:
            check_no_sol(key, kill[0])
            reasons[kill[0]] = reasons.get(kill[0], 0) + 1
            continue
        bs = None  # prime splits churn in 3-D; deepening + capped pins suffice
        if bs is not None:
            (surv, _k), p, n = bs
            if surv <= 12 or surv <= 0.34 * n ** 3:
                nM = M * n
                for sL in range(n):
                    cL = (rhoL + sL * M) % nM
                    for s1 in range(n):
                        c1 = (rho1 + s1 * M) % nM
                        for s2 in range(n):
                            c2 = (rho2 + s2 * M) % nM
                            sg = signature3(K, cL, c1, c2, nM)
                            Tv = (pow(10, cL, p) + 9 * pow(10, c1, p) + 9 * pow(10, c2, p) + K) * pow(pow(2, t0, p), -1, p) % p
                            if could(Tv, p, sg, O3[p], O7[p]):
                                stack.append((cL, c1, c2, nM, ph + 1))
                continue
        # deepen: cycle coordinates; mult chosen by unbounded signature side
        ua = a_hi is None; uw = w_hi is None
        if ua and not uw: mult = 3
        elif uw and not ua: mult = 7
        else: mult = 3 if ph % 2 == 0 else 7
        which = ph % 3
        nM = M * mult
        if nM > MAXM:
            residual.append(key); continue
        rs = [rhoL, rho1, rho2]
        for s in range(mult):
            nr = list(rs)
            nr[which] = (nr[which] + s * M) % nM
            stack.append((nr[0], nr[1], nr[2], nM, ph + 1))
    return dict(status="CLOSED", nc=nc, recorded=sorted(set(recorded)), reasons=reasons,
                residual=residual)

def brute_twofar(S, LMAX):
    K = 9 * S - 1
    p10 = [10 ** i for i in range(LMAX + 2)]
    out = []
    for L in range(5, LMAX + 1):
        base = p10[L] + K
        for q1 in range(3, L - 1):
            b2 = base + 9 * p10[q1]
            for q2 in range(q1 + 1, L):
                if smooth237(b2 + 9 * p10[q2]):
                    out.append((L, q1, q2))
    return out

def brute_slice(LMAX, Kp, A, qmin):
    p10 = [10 ** i for i in range(LMAX + 2)]
    out = []
    for L in range(qmin + 1, LMAX + 1):
        base = p10[L] + Kp
        for q in range(qmin, L):
            if smooth237(base + A * p10[q]):
                out.append((L, q))
    return out

def sieve1d(Kp, tp, Lmin, brute, pinm=()):
    """1-D: 10^L + Kp = 2^tp 3^a 7^w, L >= Lmin; classes rho mod M."""
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
        j = vp(M, 3); m3 = 3 ** (j + 2)
        X = (pow(10, rho, m3) + Kp) % m3
        e3 = vp(X, 3) if X else j + 2
        a = (e3, e3) if e3 <= j + 1 else (j + 2, None)
        i = vp(M, 7); m7 = 7 ** (i + 1)
        Y = (pow(10, rho, m7) + Kp) % m7
        e7 = vp(Y, 7) if Y else i + 1
        w = (e7, e7) if e7 <= i else (i + 1, None)
        sig = (a, w)
        if a[1] is not None and w[1] is not None:
            N0 = 2 ** tp * 3 ** a[0] * 7 ** w[0]
            L = is_power10(N0 - Kp) if N0 > Kp else None
            if L is not None and L >= Lmin and L % M == rho % M and 10 ** L + Kp == N0:
                recorded.append(L)
            reasons["size"] = reasons.get("size", 0) + 1
            continue
        killed = None
        for p in PORDER[:KILL_SCAN]:
            d = ORD10[p]
            if M % d == 0 and (pow(10, rho, p) + Kp) % p == 0:
                killed = ("T0", p); break
        if not killed:
            for p in PORDER[:KILL_SCAN]:
                d = ORD10[p]; g = math.gcd(M, d)
                if d // g > 4096: continue
                alive = False
                for gg in range(rho % g, d, g):
                    T = (pow(10, gg, p) + Kp) * inv2[p] % p
                    if could(T, p, sig, O3[p], O7[p]):
                        alive = True; break
                if not alive:
                    killed = ("prime", p); break
        if not killed:
            for m in pinm:
                # 2^tp 3^a 7^w ≡ Kp (mod m); isolate 3^a 7^w
                if m % 2 == 0:
                    continue
                x0 = Kp * pow(pow(2, tp, m), -1, m) % m
                if not could(x0, m, sig, ord_pp(3, 5, vp(m, 5)), ord_pp(7, 5, vp(m, 5))):
                    killed = ("pin", f"5^{vp(m,5)}"); break
        if killed:
            check_no_sol(rho, M, killed[0])
            reasons[killed[0]] = reasons.get(killed[0], 0) + 1
            continue
        mult = 3 if (a[1] is None and (w[1] is not None or vp(M, 3) <= vp(M, 7))) else 7
        nM = M * mult
        if nM > MAXM:
            return dict(status="RESIDUAL", cls=(rho, M), nc=nc, recorded=recorded, reasons=reasons)
        for s in range(mult):
            stack.append(((rho + s * M) % nM, nM))
    return dict(status="CLOSED", nc=nc, recorded=sorted(set(recorded)), reasons=reasons)

if __name__ == "__main__":
    # ---- 3-D sieves ----
    for S in (10, 1):
        brute = brute_twofar(S, LCHECK)
        bruteS = set(brute)
        qlo = 4 if S == 1 else 3
        t0 = vp(9 * S - 1, 2)
        print(f"two-far S_low={S}: brute solutions L<={LCHECK}: {brute}", flush=True)
        res = sieve3d(9 * S - 1, t0, qlo, brute)
        print(f"  3-D sieve (q1>={qlo}): {res['status']} nc={res['nc']} "
              f"recorded={res['recorded']} reasons={res['reasons']} residual={len(res.get('residual', []))}",
              flush=True)
        import json
        json.dump(res.get('residual', []), open(f'residual_3d_S{S}.json', 'w'))
    # ---- S=1, q1=3 slice: 10^L + 9*10^q2 + 9008 ----
    # corners
    for (L, q2) in [(5, 4), (6, 4)]:
        X = 10 ** L + 9 * 10 ** q2 + 9008
        print(f"  q1=3 corner (L={L},q2={q2}): X={X} smooth={smooth237(X)}")
    # q2 = 4, L >= 7: t = 6 pinned; verify
    for L in range(7, 150):
        assert vp(10 ** L + 9 * 10 ** 4 + 9008, 2) == 6, f"t-claim q2=4 fails at L={L}"
    brute = [(L, q) for (L, q) in brute_slice(600, 99008, 9, 4) if L >= 7]
    res = sieve1d(99008, 6, 7, [(L,) for (L, q) in brute], pinm=(5 ** 4,))
    print(f"  q1=3, q2=4 slice (K=99008, t=6, L>=7): {res['status']} nc={res['nc']} "
          f"recorded={res['recorded']} reasons={res['reasons']} brute={brute}", flush=True)
    # q2 >= 5: t = 4 pinned; verify
    for L in range(6, 150):
        for q2 in range(5, min(L, 12)):
            assert vp(10 ** L + 9 * 10 ** q2 + 9008, 2) == 4, f"t-claim q2>=5 fails at {(L,q2)}"
    brute = brute_slice(600, 9008, 9, 5)
    import importlib.util
    spec = importlib.util.spec_from_file_location("p2s", os.path.join(os.path.dirname(os.path.abspath(__file__)), "p2_sieve.py"))
    p2s = importlib.util.module_from_spec(spec); spec.loader.exec_module(p2s)
    ctx = p2s.CtxK(K=9008, A=9, t0=4, qlo=5)
    res2 = p2s.sieve(ctx, brute=brute)
    print(f"  q1=3, q2>=5 slice (K=9008, t=4, q>=5): {res2['status']} nc={res2['nc']} "
          f"recorded={res2['recorded']} reasons={res2.get('reasons')}", flush=True)
