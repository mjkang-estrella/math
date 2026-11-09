# r8 check_cert2d.py — SMALL independent checker for the 2-D one-far mixed certificates.
#
#   usage: python3 check_cert2d.py cert2d_S<A>_...jsonl   (or any cert file)
#
# Certifies: the only (L, q) with L > q >= qmin and
#   2^t 3^a 7^w = 10^L + A*10^q + K   (t = t0 = v2(K), valid since q >= qmin > t0)
# are the recorded solutions.
#
# Fresh implementation: recomputes every signature from (10^rL + A*10^rq + K) directly,
# re-verifies tree coverage (every lift of every internal node is a child or is
# re-killed via rest at the child modulus), re-tests every kill (T0 / prime region
# with aligned 2-D lifts / pin by explicit coset sets / sz by exact big-int comparison),
# and direct-evaluates every recorded solution.
import json, math, sys

fn = sys.argv[1]
lines = [l for l in open(fn).read().split("\n") if l.strip()]
meta = json.loads(lines[0])
assert meta["k"] == "meta"
A, K, Q0 = meta["A"], meta["K"], meta["qmin"]
nodes = [json.loads(l) for l in lines[1:]]

def vp(n, p):
    c = 0
    while n % p == 0:
        n //= p; c += 1
    return c

t0 = vp(K, 2)
assert Q0 == max(3, t0 + 1), "qmin must be the domain floor"

def fac(n):
    f = {}; p = 2
    while p * p <= n:
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def order(g, q):
    o = q - 1
    for p in fac(q - 1):
        while o % p == 0 and pow(g, o // p, q) == 1: o //= p
    return o

def signature(rL, rq, ML, MQ):
    j = min(vp(ML, 3), vp(MQ, 3)); m = 3 ** (j + 2)
    X = (pow(10, rL, m) + A * pow(10, rq, m) + K) % m
    a = (vp(X, 3), vp(X, 3)) if X else (j + 2, None)
    if a[0] <= j + 1: a = (a[0], a[0])
    else: a = (j + 2, None)
    if ML % 6 or MQ % 6:
        w = (0, None)
    else:
        i = min(vp(ML, 7), vp(MQ, 7)); m = 7 ** (i + 1)
        Y = (pow(10, rL, m) + A * pow(10, rq, m) + K) % m
        e = vp(Y, 7) if Y else i + 1
        w = (e, e) if e <= i else (i + 1, None)
    return a, w

def possible(p, T, sig):
    """False  =>  T not ≡ 3^a 7^w (mod p) for any a,w in the signature ranges."""
    if T % p == 0:
        return False
    (a_lo, a_hi), (w_lo, w_hi) = sig
    x = T * pow(pow(3, a_lo, p), -1, p) % p
    x = x * pow(pow(7, w_lo, p), -1, p) % p
    if a_hi is None and w_hi is None:
        e = order(3, p) * order(7, p) // math.gcd(order(3, p), order(7, p))
        return pow(x, e, p) == 1
    if a_hi is None: return pow(x, order(3, p), p) == 1
    if w_hi is None: return pow(x, order(7, p), p) == 1
    return x == 1

def crt_lift(r, M, gg, d):
    g = math.gcd(M, d); b = d // g
    t = ((gg - r) // g) * pow(M // g, -1, b) % b
    return (r + M * t) % (M * b)

def kill_prime(p, rL, rq, ML, MQ):
    """True iff no solution of the equation can have (L,q) in the class (t = t0)."""
    assert p not in (2, 3, 5, 7), "kill prime must be outside {2,3,5,7}"
    d = order(10, p)
    gL, gQ = math.gcd(ML, d), math.gcd(MQ, d)
    nL, nQ = d // gL, d // gQ
    inv2 = pow(pow(2, t0, p), -1, p)
    for ggL in range(rL % gL, d, gL):
        for ggQ in range(rq % gQ, d, gQ):
            T = (pow(10, ggL, p) + A * pow(10, ggQ, p) + K) * inv2 % p
            if nL * nQ == 1:
                sg = signature(rL, rq, ML, MQ)
            else:
                sg = signature(crt_lift(rL, ML, ggL, d), crt_lift(rq, MQ, ggQ, d),
                               ML * nL, MQ * nQ)
            if possible(p, T, sg):
                return False
    return True

def kill_T0(p, rL, rq, ML, MQ):
    assert p not in (2, 3, 5, 7), "kill prime must be outside {2,3,5,7}"
    d = order(10, p)
    if ML % d or MQ % d:
        return False
    return (pow(10, rL, p) + A * pow(10, rq, p) + K) % p == 0

def ord_pp(a, p, k):
    if k <= 0: return 1
    o = 1; x = a % p
    while x != 1:
        x = x * a % p; o += 1
    pk = p
    for _ in range(k - 1):
        pk *= p
        if pow(a, o, pk) != 1: o *= p
    return o

def q_minimum(kappa, MQ, qlo):
    q = kappa % MQ
    while q < qlo: q += MQ
    return q

def pin_kill(sig, qp, exact, rq, MQ):
    """True iff 3^a 7^w ≡ K/2^t0 (mod 2^{qp-t0} 5^{qp}) is unsolvable for (a,w) in sig."""
    # validity: every class point has q >= qp
    assert qp <= q_minimum(rq, MQ, Q0), ("pin modulus above class q-minimum", qp)
    N2, N5 = 2 ** (qp - t0), 5 ** qp
    N = N2 * N5
    K2 = K // 2 ** t0
    if exact:
        assert N <= 10 ** 6, "exact pin set too large"
        c2, c5 = K2 % N2, K2 * pow(pow(2, t0, N5), -1, N5) % N5
        C = (c2 + N2 * ((c5 - c2) * pow(N2, -1, N5) % N5)) % N
        (a_lo, a_hi), (w_lo, w_hi) = sig
        gens = ([3] if a_hi is None else []) + ([7] if w_hi is None else [])
        S = {1}
        frontier = [1]
        while frontier:
            x = frontier.pop()
            for g in gens:
                y = x * g % N
                if y not in S:
                    S.add(y); frontier.append(y)
        if a_hi is not None: S = {x * pow(3, a_hi, N) % N for x in S}
        if w_hi is not None: S = {x * pow(7, w_hi, N) % N for x in S}
        return C not in S
    K2m = K2
    for base, e in ((2, qp - t0), (5, qp)):
        if e < 1: continue
        m = base ** e
        x0 = K2m % m if base == 2 else K2 * pow(pow(2, t0, m), -1, m) % m
        (a_lo, a_hi), (w_lo, w_hi) = sig
        x = x0 * pow(pow(3, a_lo, m), -1, m) % m
        x = x * pow(pow(7, w_lo, m), -1, m) % m
        if a_hi is None and w_hi is None:
            o3, o7 = ord_pp(3, base, e), ord_pp(7, base, e)
            if pow(x, o3 * o7 // math.gcd(o3, o7), m) != 1:
                return True
        elif a_hi is None:
            if pow(x, ord_pp(3, base, e), m) != 1:
                return True
        elif w_hi is None:
            if pow(x, ord_pp(7, base, e), m) != 1:
                return True
        else:
            if x != 1:
                return True
    return False

nleaf = nrest = nmism = 0
sols = []

def verify(idx):
    global nleaf, nrest, nmism
    nd = nodes[idx]
    rL, rq = nd["r"]; ML, MQ = nd["m"]
    if nd["k"] == "l":
        nleaf += 1
        a, w = signature(rL, rq, ML, MQ)
        if [list(a), list(w)] != [nd["a"], nd["w"]]:
            nmism += 1
        x = nd["x"]
        if "T0" in x:
            assert kill_T0(x["T0"], rL, rq, ML, MQ), ("T0 kill fails", nd)
        elif "prime" in x:
            assert kill_prime(x["prime"], rL, rq, ML, MQ), ("prime kill fails", nd)
        elif "pin" in x:
            qp, exact = x["pin"]
            assert pin_kill((a, w), qp, exact, rq, MQ), ("pin kill fails", nd)
        elif "sz" in x:
            (a0, a1), (w0, w1) = a, w
            assert a1 is not None and w1 is not None and a0 == a1 and w0 == w1, ("sz needs exact", nd)
            N0 = 2 ** t0 * 3 ** a0 * 7 ** w0
            for L, q in x["L"]:
                assert L % ML == rL % ML and q % MQ == rq % MQ, ("recorded not in class", nd, L, q)
                assert 10 ** L + A * 10 ** q + K == N0, ("recorded solution false", nd, L, q)
                sols.append((L, q))
        else:
            raise ValueError(nd)
        return
    ch = [nodes[i] for i in nd["c"]]
    Ms = {tuple(c["m"]) for c in ch}
    assert len(Ms) == 1, "children must share one modulus pair"
    ML2, MQ2 = ch[0]["m"]
    assert ML2 % ML == 0 and MQ2 % MQ == 0 and (ML2, MQ2) != (ML, MQ)
    lifts = {(rL % ML + i * ML) % ML2 for i in range(ML2 // ML)}, \
            {(rq % MQ + j * MQ) % MQ2 for j in range(MQ2 // MQ)}
    chr_ = {(c["r"][0] % ML2, c["r"][1] % MQ2) for c in ch}
    assert len(chr_) == len(ch), "children must be distinct lifts"
    for cL in lifts[0]:
        for cQ in lifts[1]:
            if (cL, cQ) in chr_:
                continue
            assert "rest" in nd and nd["rest"], ("lift not covered", nd, cL, cQ)
            p = nd["rest"]["q"]
            assert kill_prime(p, cL, cQ, ML2, MQ2), ("rest lift survives", nd, cL, cQ)
            nrest += 1
    for i in nd["c"]:
        verify(i)

roots = [i for i, n in enumerate(nodes) if n.get("p") == -1]
assert len(roots) == 1 and tuple(nodes[roots[0]]["m"]) == (1, 1) and nodes[roots[0]]["r"] == [0, 0]
verify(roots[0])
print(f"A={A} K={K} qmin={Q0}: leaves={nleaf} rest-lifts killed={nrest} "
      f"signature mismatches={nmism} solutions(L>q>={Q0})={sorted(sols)}  -> "
      f"{'CERTIFICATE VALID' if nmism == 0 else 'INVALID'}")
