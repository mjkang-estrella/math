# r8 gen_cert17.py — emit v12-format certificates 10^L + K = 2^t 3^a 7^w for the
# 17 all-low constants closed by round 6 stage 1 (K=188, 278 done in r7).
# Engine reused from r7 gen_cert.py (same author); independent checking is v12.
# Run: bash -c 'ulimit -v 3000000; python3 -I gen_cert17.py'

import math, json, os, sys

KS = [98, 908, 989, 107, 917, 1079, 1808, 1889, 2708, 2789, 926, 1169, 197, 1817, 1979, 998, 116]
if len(sys.argv) > 1:
    KS = [int(x) for x in sys.argv[1:]]  # also used for the q=3 slice certs (9008/18008/27008)

if os.environ.get("CHECK_CONSTANTS", "1") == "1":
    # sanity: the 19 constants from r6 v2_A.py Part 1, minus {188, 278}
    import itertools
    _exp = set()
    for cv in ([1,1],[1,2],[1,3],[2,2],[1,1,1]):
        for perm in sorted(set(itertools.permutations(cv))):
            for pos in itertools.permutations(range(3), len(cv)):
                S = sum(c*10**p for c, p in zip(perm, pos))
                _exp.add(9*S - 1)
    assert len(_exp) == 19 and set(KS) <= _exp, sorted(_exp)

MAXM = 2 * 10 ** 13
KILL_SCAN = 500
ALIGN_CAP = 64
SPLIT_SCAN = 60
SPLIT_CAP = 512
NODE_CAP = 4_000_000

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

ALLP = primes_upto(50000)
PRIMES = [q for q in ALLP if q not in (2, 3, 5, 7)]

def ord_of(a, q):
    d = q - 1
    n = d
    f = 2
    while f * f <= n:
        if n % f == 0:
            while n % f == 0: n //= f
            while d % f == 0 and pow(a, d // f, q) == 1:
                d //= f
        f += 1
    if n > 1:
        while d % n == 0 and pow(a, d // n, q) == 1:
            d //= n
    return d

ORD10, O3, O7 = {}, {}, {}
for q in PRIMES:
    ORD10[q] = ord_of(10, q)
    O3[q] = ord_of(3, q)
    O7[q] = ord_of(7, q)
PORDER = sorted(PRIMES, key=lambda q: (O3[q] * O7[q] // math.gcd(O3[q], O7[q])) / (q - 1))

def signature(K, rho, M):
    j = vp(M, 3); m3 = 3 ** (j + 2)
    X = (pow(10, rho, m3) + K) % m3
    e3 = vp(X, 3) if X else j + 2
    a = (e3, e3) if e3 <= j + 1 else (j + 2, None)
    if K % 7 == 0:
        w = (0, 0)
    elif M % 6:
        w = (0, None)
    else:
        i = vp(M, 7); m7 = 7 ** (i + 1)
        Y = (pow(10, rho, m7) + K) % m7
        e7 = vp(Y, 7) if Y else i + 1
        w = (e7, e7) if e7 <= i else (i + 1, None)
    return a, w

def region_pass(q, T, sig, o3, o7):
    if T == 0:
        return False
    (a_lo, a_hi), (w_lo, w_hi) = sig
    x = T * pow(pow(3, a_lo, q), -1, q) % q
    x = x * pow(pow(7, w_lo, q), -1, q) % q
    if a_hi is None and w_hi is None:
        return pow(x, o3 * o7 // math.gcd(o3, o7), q) == 1
    if a_hi is None:
        return pow(x, o3, q) == 1
    if w_hi is None:
        return pow(x, o7, q) == 1
    return x == 1

def small_sols(K, T0, rho, M):
    return [L0 for L0 in range(T0 + 1) if L0 % M == rho % M and smooth237(10 ** L0 + K)]

def try_kill(K, T0, INV, rho, M, sig):
    for q in PORDER[:KILL_SCAN]:
        d = ORD10[q]
        if M % d == 0 and (pow(10, rho, q) + K) % q == 0:
            return ("T0", q)
    for q in PORDER[:KILL_SCAN]:
        d = ORD10[q]
        if M % d == 0:
            T = (pow(10, rho, q) + K) * INV[q] % q
            if not region_pass(q, T, sig, O3[q], O7[q]):
                return ("prime", q)
        else:
            g = math.gcd(M, d)
            if d // g > ALIGN_CAP:
                continue
            alive = False
            for gg in range(rho % g, d, g):
                T = (pow(10, gg, q) + K) * INV[q] % q
                if region_pass(q, T, sig, O3[q], O7[q]):
                    alive = True; break
            if not alive:
                return ("prime", q)
    return None

def best_split(K, T0, INV, rho, M):
    best = None
    for q in PORDER[:SPLIT_SCAN]:
        d = ORD10[q]; g = math.gcd(M, d); nc = d // g
        if nc < 2 or nc > SPLIT_CAP or M * nc > MAXM:
            continue
        Mc = M * nc
        killed = 0
        for k in range(nc):
            ck = (rho + k * M) % Mc
            Tk = (pow(10, ck, q) + K) * INV[q] % q
            if not region_pass(q, Tk, signature(K, ck, Mc), O3[q], O7[q]):
                killed += 1
        if killed == 0:
            continue
        surv = nc - killed
        key = (surv, -killed)
        if best is None or key < best[0]:
            best = (key, q, nc)
    return best

def run(K):
    T0 = 0
    while K % (2 ** (T0 + 1)) == 0:
        T0 += 1
    INV = {q: pow(pow(2, T0, q), -1, q) for q in PRIMES}
    nodes = []
    def emit(d):
        nodes.append(d)
        return len(nodes) - 1

    def resolve_exact(rho, M, sig):
        (a0, _), (w0, _) = sig
        N0 = 2 ** T0 * 3 ** a0 * 7 ** w0
        rec = set(small_sols(K, T0, rho, M))
        if N0 > K:
            r = N0 - K; e = 0
            while r % 10 == 0:
                r //= 10; e += 1
            if r == 1:
                L = e
                if L % M == rho % M and (10 ** L + K == N0):
                    rec.add(L)
        return {"k": "l", "r": rho, "m": M,
                "a": [sig[0][0], sig[0][1]], "w": [sig[1][0], sig[1][1]],
                "x": {"sz": [a0, w0], "L": sorted(rec)}}

    def process(rho, M, parent, depth=0):
        assert len(nodes) < NODE_CAP, "node cap exceeded"
        assert depth < 500, "depth exceeded"
        sig = signature(K, rho, M)
        small = small_sols(K, T0, rho, M)
        (a_lo, a_hi), (w_lo, w_hi) = sig
        if a_hi is not None and w_hi is not None:
            d = resolve_exact(rho, M, sig)
            d["p"] = parent
            return emit(d)
        kill = None if small else try_kill(K, T0, INV, rho, M, sig)
        if kill:
            kind, q = kill
            d = {"k": "l", "r": rho, "m": M,
                 "a": [a_lo, a_hi], "w": [w_lo, w_hi], "x": {kind: q}, "p": parent}
            return emit(d)
        bs = best_split(K, T0, INV, rho, M)
        use_split = False
        if bs is not None:
            (surv, _negk), q, nc = bs
            frac = 1 - surv / nc
            if surv <= 3 or frac >= 0.9:
                use_split = True
        if use_split:
            _, q, nc = bs
            Mc = M * nc
            surv = []
            for k in range(nc):
                ck = (rho + k * M) % Mc
                Tk = (pow(10, ck, q) + K) * INV[q] % q
                ksmall = any(L0 % Mc == ck for L0 in small)
                if ksmall or region_pass(q, Tk, signature(K, ck, Mc), O3[q], O7[q]):
                    surv.append(ck)
            if surv:   # L2b patch: if no child survives, fall through to deepen
                nd = {"k": "i", "p": parent, "r": rho, "m": M, "c": [], "rest": None}
                nid = emit(nd)
                for ck in surv:
                    nd["c"].append(process(ck, Mc, nid, depth + 1))
                if len(surv) < nc:
                    nd["rest"] = {"q": q}
                return nid
        ua = a_hi is None; uw = w_hi is None
        if ua and not uw: mult = 3
        elif uw and not ua: mult = 7
        else: mult = 3 if (rho + depth) % 2 == 0 else 7
        Mc = M * mult
        nd = {"k": "i", "p": parent, "r": rho, "m": M, "c": [], "rest": None}
        nid = emit(nd)
        for k in range(mult):
            ck = (rho + k * M) % Mc
            nd["c"].append(process(ck, Mc, nid, depth + 1))
        return nid

    sys.setrecursionlimit(100000)
    root = {"k": "i", "p": -1, "r": 0, "m": 1, "c": [], "rest": None}
    rid = emit(root)
    for rho in range(6):
        root["c"].append(process(rho, 6, rid))

    n_leaves = sum(1 for d in nodes if d["k"] == "l")
    n_rest = sum(1 for d in nodes if d["k"] == "i" and d.get("rest"))
    sols = sorted({L for d in nodes if d["k"] == "l" and "sz" in d["x"] for L in d["x"]["L"]})
    path = f"cert_K{K}.jsonl"
    with open(path, "w") as f:
        for d in nodes:
            f.write(json.dumps(d) + "\n")
    print(f"K={K}: nodes={len(nodes)} leaves={n_leaves} rest={n_rest} recorded={sols} bytes={os.path.getsize(path)}", flush=True)

for K in KS:
    run(K)
print("ALL DONE")
