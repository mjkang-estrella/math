"""Stage 2: refine stage-1 survivors mod M2 = M1 * 17 * 5882353 * 9999999900000001.

Positions: mod 24 -> 48.  (u+2, w): mod (O3_1, O7_1) -> mod (O3_2, O7_2).
New primes p, with (sigma3_p, sigma7_p) = periods of k_u -> 3^(O3_1 k_u), k_w -> 7^(O7_1 k_w):
  p=17:              (2, 1)           -- enumerative
  p=5882353:         (122549, 17507)  -- enumerative
  p=9999999900000001:(1.0e8, 2.5e11)  -- 2-var congruence via Pohlig-Hellman (p-1 smooth)

A survivor class records: positions mod 48, t, (U1,W1), the combined k_u class
(ku_res mod ku_mod), the combined k_w class from the enumerative primes, and the
big-prime congruence (a,b,c,N).  From these we compute the minimal possible n.
"""
import sys, time, random
from math import gcd
from cascade import M0, M1, O3_0, O7_0, O3_1, O7_1, solve_2d_prime, crt1
from ntlib import factorint, invmod, order_fast

M2 = M1 * 17 * 5882353 * 9999999900000001

def build_stage2_params():
    params = []
    for p in (17, 5882353, 9999999900000001):
        o3p, o7p = order_fast(3, p, p - 1), order_fast(7, p, p - 1)
        s3 = o3p // gcd(O3_1, o3p)
        s7 = o7p // gcd(O7_1, o7p)
        params.append(dict(p=p, o3p=o3p, o7p=o7p, s3=s3, s7=s7))
    return params

def build_kw_tables(params):
    """dict {B^kw mod p: kw} for the enumerative primes, kw in [0, s7)."""
    tables = {}
    for pr in params:
        if pr['p'] == 9999999900000001: continue
        B = pow(7, O7_1, pr['p'])
        tbl = {}
        x = 1
        for kw in range(pr['s7']):
            if x not in tbl: tbl[x] = kw
            x = x * B % pr['p']
        tables[pr['p']] = tbl
    return tables

# ---------------- Pohlig-Hellman for the big prime ----------------
def bsgs(g, h, p, order):
    if h == 1: return 0
    m = int(order ** 0.5) + 1
    tbl = {}
    x = 1
    for j in range(m):
        tbl.setdefault(x, j)
        x = x * g % p
    gm = invmod(pow(g, m, p), p)
    y = h
    for i in range(m + 1):
        if y in tbl:
            return (i * m + tbl[y]) % order
        y = y * gm % p
    raise ValueError("bsgs failed")

def qsub_dlog(p, q, val):
    """dlog of val in the cyclic subgroup of order q (q = prime power), base a generator."""
    if val == 1: return 0
    while True:
        h = random.randrange(2, p - 1)
        g = pow(h, (p - 1) // q, p)
        if g == 1 or order_fast(g, p, p - 1) != q: continue
        return bsgs(g, val, p, q)

def two_var_congruence(p, A, B, C):
    """A^x B^y = C (mod p)  <=>  a x + b y = c (mod N), N = p-1.  Returns (a,b,c,N)
    or None if unsolvable.  Requires p-1 smooth."""
    N = p - 1
    a = b = c = 0; N2 = 1
    for q, f in factorint(N).items():
        qq = q ** f
        Aq, Bq, Cq = pow(A, N // qq, p), pow(B, N // qq, p), pow(C, N // qq, p)
        aq = qsub_dlog(p, qq, Aq); bq = qsub_dlog(p, qq, Bq); cq = qsub_dlog(p, qq, Cq)
        r = (_crt3(a, N2, aq, qq), _crt3(b, N2, bq, qq), _crt3(c, N2, cq, qq))
        if any(x is None for x in r): return None
        a, b, c = r
        N2 *= qq
    if c % gcd(gcd(a, b), N) != 0:
        return None
    return (a, b, c, N2)

def _crt3(x1, m1, x2, m2):
    g = gcd(m1, m2)
    if (x2 - x1) % g: return None
    l = m1 // g * m2
    m1g, m2g = m1 // g, m2 // g
    t = ((x2 - x1) // g) * invmod(m1g % m2g, m2g) % m2g
    return (x1 + m1 * t) % l

def ku_projection(a, b, c, N):
    """k_u admitting a k_w solution: gcd(b,N) | c - a*k_u.  Returns (x0, P) with
    k_u = x0 (mod P), or None."""
    D = gcd(b, N)
    g = gcd(a, D)
    if c % g: return None
    P = D // g
    x0 = ((c // g) * invmod((a // g) % P, P)) % P if P > 1 else 0
    return (x0, P)

# ---------------- stage 2 main ----------------
def stage2(surv1, delta, params, kw_tables, verbose=True):
    O3_2, O7_2 = O3_1, O7_1
    for pr in params:
        O3_2 = O3_2 * pr['o3p'] // gcd(O3_2, pr['o3p'])
        O7_2 = O7_2 * pr['o7p'] // gcd(O7_2, pr['o7p'])
    p10 = [pow(10, i, M2) for i in range(48)]
    c = 9 * (delta - 1)
    inv2t_cache = {}
    out = []
    t0 = time.time()
    s17 = params[0]; s588 = params[1]
    for (L24, e24, t, U1, W1, hu, hw) in surv1:
        if t not in inv2t_cache: inv2t_cache[t] = invmod(pow(2, t, M2), M2)
        it2 = inv2t_cache[t]
        for L48 in (L24, L24 + 24):
            for e48 in (e24, e24 + 24):
                lhs = (p10[L48] + c * p10[e48] - 1) % M2
                V = lhs * it2 % M2
                big = None
                # big prime first (cheap O(1)-ish via PH) as a strong filter
                A = pow(3, O3_1, 9999999900000001); B = pow(7, O7_1, 9999999900000001)
                prb = params[2]
                base = pow(3, U1 % prb['o3p'], 9999999900000001) * pow(7, W1 % prb['o7p'], 9999999900000001) % 9999999900000001
                target = V * invmod(base, 9999999900000001) % 9999999900000001
                big = two_var_congruence(9999999900000001, A, B, target)
                if big is None: continue
                (a, b, cN, N) = big
                kc = ku_projection(a, b, cN, N)
                if kc is None: continue
                # p=17 classes
                p = 17
                t17 = V * invmod(pow(3, U1 % s17['o3p'], p) * pow(7, W1 % s17['o7p'], p) % p, p) % p
                A17, B17 = pow(3, O3_1, p), pow(7, O7_1, p)
                sols17 = solve_2d_prime(p, A17, B17, t17, s17['s3'], s17['s7'])
                if not sols17: continue
                # p=5882353 classes
                p = 5882353
                t58 = V * invmod(pow(3, U1 % s588['o3p'], p) * pow(7, W1 % s588['o7p'], p) % p, p) % p
                A58 = pow(3, O3_1, p)
                tbl = kw_tables[p]
                Ainv = invmod(A58, p)
                sols588 = []
                x = t58
                for ku in range(s588['s3']):
                    kw = tbl.get(x)
                    if kw is not None: sols588.append((ku, kw))
                    x = x * Ainv % p
                if not sols588: continue
                emitted = set()
                for (ku17, kw17) in sols17:
                    for (ku588, kw588) in sols588:
                        k1 = crt1(ku17, s17['s3'], ku588, s588['s3'])
                        if k1 is None: continue
                        k2 = crt1(k1[0], k1[1], kc[0], kc[1])
                        if k2 is None: continue
                        kw1 = crt1(kw17, s17['s7'], kw588, s588['s7'])
                        if kw1 is None: continue
                        key = (k2[0], k2[1], kw1[0], kw1[1])
                        if key in emitted: continue
                        emitted.add(key)
                        ku_res, ku_mod = k2
                        out.append(dict(L48=L48 % 48, e48=e48 % 48, t=t,
                                        U1=U1, W1=W1, ku_res=ku_res, ku_mod=ku_mod,
                                        kw_res=kw1[0], kw_mod=kw1[1],
                                        big_cong=big, O3_2=O3_2, O7_2=O7_2))
    if verbose: print(f"    stage2 survivors: {len(out)}  ({time.time()-t0:.1f}s)", flush=True)
    return out

def minimal_n_bound(surv):
    """Lower bound for n = 2^t 3^u 7^w over the survivor class; returns (n_lb, u_min, w_min)."""
    t = surv['t']; U1 = surv['U1']; W1 = surv['W1']
    ku_res, ku_mod = surv['ku_res'], surv['ku_mod']
    kw_res, kw_mod = surv['kw_res'], surv['kw_mod']
    O3_2, O7_2 = surv['O3_2'], surv['O7_2']
    u2_min = U1 + O3_1 * ku_res
    while u2_min < 2: u2_min += O3_2
    u_min = u2_min - 2
    w_min = W1 + O7_1 * kw_res
    if w_min < 0: w_min += O7_2
    return 2**t * 3**u_min * 7**w_min, u_min, w_min
