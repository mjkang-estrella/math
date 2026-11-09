# r7 gen_cert.py — certificate generator for the round-6 (A) sieve, K in {188, 278}.
#
# Emits a JSON-lines certificate: a partition tree of all L >= 0 for the equation
#   10^L + K = 2^t * 3^a * 7^w .
# Internal node: {"k":"i","p":parent,"r":rho,"m":M,"c":[child ids],"rest":{"q":q}|null}
#   children all have modulus M*mult and residues {(rho + k*M) mod M*mult : k < mult};
#   any child residue NOT in "c" is a killed subclass, verified via "rest".
# Leaf: {"k":"l","p":parent,"r":rho,"m":M,"a":[lo,hi],"w":[lo,hi],"x":reason}
#   reason: {"T0":q} | {"prime":q} | {"sz":[a0,w0],"L":[verified solution Ls]}
#
# Signatures are computed DIRECTLY from 10^rho+K mod 3^{j+2} / mod 7^{i+1}
# (j = v3(M), i = v7(M), 6 | M) — no ladders, matching the independent checker.
# Run: bash -c 'ulimit -v 3000000; python3 -I gen_cert.py 188'

import math, json, sys, os

K = int(sys.argv[1]) if len(sys.argv) > 1 else 188
T0 = 0
while K % (2 ** (T0 + 1)) == 0:
    T0 += 1

MAXM = 2 * 10 ** 13
KILL_SCAN = 500          # primes scanned per kill attempt
ALIGN_CAP = 64           # max d/g for whole-class aligned kill attempts
SPLIT_SCAN = 60          # primes simulated per split search
SPLIT_CAP = 512          # max children per prime split
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
    # order of a mod q via factoring q-1
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
INV2T0 = {q: pow(pow(2, T0, q), -1, q) for q in PRIMES}

def signature(rho, M):
    """((a_lo,a_hi),(w_lo,w_hi)) valid uniformly on {L ≡ rho mod M}; hi None = unbounded."""
    j = vp(M, 3); m3 = 3 ** (j + 2)
    X = (pow(10, rho, m3) + K) % m3
    e3 = vp(X, 3) if X else j + 2
    a = (e3, e3) if e3 <= j + 1 else (j + 2, None)
    i = vp(M, 7); m7 = 7 ** (i + 1)
    Y = (pow(10, rho, m7) + K) % m7
    e7 = vp(Y, 7) if Y else i + 1
    w = (e7, e7) if e7 <= i else (i + 1, None)
    return a, w

def region_pass(q, T, sig, o3, o7):
    """True iff T ≡ 3^a 7^w (mod q) is possible for some a,w in the signature ranges."""
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

def small_sols(rho, M):
    return [L0 for L0 in range(T0 + 1) if L0 % M == rho % M and smooth237(10 ** L0 + K)]

def try_kill(rho, M, sig):
    # pass 1: T0 kills (cheapest, valid for every L in the class)
    for q in PORDER[:KILL_SCAN]:
        d = ORD10[q]
        if M % d == 0 and (pow(10, rho, q) + K) % q == 0:
            return ("T0", q)
    # pass 2: region kills
    for q in PORDER[:KILL_SCAN]:
        d = ORD10[q]
        if M % d == 0:
            T = (pow(10, rho, q) + K) * INV2T0[q] % q
            if not region_pass(q, T, sig, O3[q], O7[q]):
                return ("prime", q)
        else:
            g = math.gcd(M, d)
            if d // g > ALIGN_CAP:
                continue
            alive = False
            for gg in range(rho % g, d, g):
                T = (pow(10, gg, q) + K) * INV2T0[q] % q
                if region_pass(q, T, sig, O3[q], O7[q]):
                    alive = True; break
            if not alive:
                return ("prime", q)
    return None

def best_split(rho, M):
    best = None
    for q in PORDER[:SPLIT_SCAN]:
        d = ORD10[q]; g = math.gcd(M, d); nc = d // g
        if nc < 2 or nc > SPLIT_CAP or M * nc > MAXM:
            continue
        Mc = M * nc
        killed = 0
        for k in range(nc):
            ck = (rho + k * M) % Mc
            Tk = (pow(10, ck, q) + K) * INV2T0[q] % q
            if not region_pass(q, Tk, signature(ck, Mc), O3[q], O7[q]):
                killed += 1
        if killed == 0:
            continue
        surv = nc - killed
        key = (surv, -killed)
        if best is None or key < best[0]:
            best = (key, q, nc)
    return best  # None or (key, q, nc)

nodes = []
_ids = {}
def emit(d):
    nodes.append(d)
    i = len(nodes) - 1
    _ids[id(d)] = i
    return i

def resolve_exact(rho, M, sig):
    (a0, _), (w0, _) = sig
    N0 = 2 ** T0 * 3 ** a0 * 7 ** w0
    rec = set(small_sols(rho, M))
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
    sig = signature(rho, M)
    small = small_sols(rho, M)
    (a_lo, a_hi), (w_lo, w_hi) = sig
    if a_hi is not None and w_hi is not None:
        d = resolve_exact(rho, M, sig)
        d["p"] = parent
        return emit(d)
    kill = None if small else try_kill(rho, M, sig)
    if kill:
        kind, q = kill
        d = {"k": "l", "r": rho, "m": M,
             "a": [a_lo, a_hi], "w": [w_lo, w_hi], "x": {kind: q}, "p": parent}
        return emit(d)
    # no whole-class kill: split by best prime, else deepen
    bs = best_split(rho, M)
    use_split = False
    if bs is not None:
        (surv, _negk), q, nc = bs
        frac = 1 - surv / nc
        if surv <= 3 or frac >= 0.9:
            use_split = True
    if use_split:
        _, q, nc = bs
        Mc = M * nc
        nd = {"k": "i", "p": parent, "r": rho, "m": M, "c": [], "rest": None}
        nid = emit(nd)
        any_killed = False
        for k in range(nc):
            ck = (rho + k * M) % Mc
            Tk = (pow(10, ck, q) + K) * INV2T0[q] % q
            ksmall = any(L0 % Mc == ck for L0 in small)
            if not ksmall and not region_pass(q, Tk, signature(ck, Mc), O3[q], O7[q]):
                any_killed = True
                continue
            nd["c"].append(process(ck, Mc, nid, depth + 1))
        if any_killed:
            nd["rest"] = {"q": q}
        return nid
    # deepen
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
print(f"K={K}: nodes={len(nodes)} leaves={n_leaves} internal={len(nodes)-n_leaves} rest={n_rest}", flush=True)
kinds = {}
for d in nodes:
    if d["k"] == "l":
        key = tuple(sorted(d["x"].keys()))
        kinds[key] = kinds.get(key, 0) + 1
print("leaf reasons:", kinds)
sols = sorted({L for d in nodes if d["k"] == "l" and "sz" in d["x"] for L in d["x"]["L"]})
print("recorded solutions:", sols)
path = f"cert_K{K}.jsonl"
with open(path, "w") as f:
    for d in nodes:
        f.write(json.dumps(d) + "\n")
print("wrote", path, os.path.getsize(path), "bytes")
