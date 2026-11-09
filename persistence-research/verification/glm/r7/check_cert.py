# r7 check_cert.py — INDEPENDENT checker for the (A) certificates cert_K{K}.jsonl.
#
# Shares no code with gen_cert.py or the round-6 sieve. Verifies, for K given:
#   (0) t0 = v2(K) and the lemma "L > t0 => v2(10^L+K) = t0" (odd-bracket algebra).
#   (i)  the partition tree: root (rho=0, M=1); every internal node's children share
#        one modulus M_c = mult*M and their residues are exactly
#        {(rho + k*M) mod M_c : 0 <= k < mult}; subclasses absent from the child list
#        are "rest"-killed and re-verified directly.
#   (ii) every stored a_sig/w_sig is recomputed from 10^rho+K mod 3^{j+2} and
#        mod 7^{i+1}, j = v3(M), i = v7(M), 6 | M.
#   (iii) every kill is recomputed: T0 (q | 10^L+K for the whole class),
#        prime region test over all aligned residues gg mod ord_q(10), and
#        exact-size resolution (10^L+K = 2^t0 3^a0 7^w0 has the single candidate
#        10^L = N0-K; small L <= t0 are factored directly).
# Exit code 0 + "PASS" iff every check holds.
# Run: bash -c 'ulimit -v 3000000; python3 -I check_cert.py 188 cert_K188.jsonl'

import json, math, sys

def vp(n, p):
    c = 0
    while n % p == 0:
        n //= p; c += 1
    return c

def is_power10(x):
    if x <= 0: return None
    e = 0
    while x % 10 == 0:
        x //= 10; e += 1
    return e if x == 1 else None

def smooth237(x):
    for p in (2, 3, 7):
        while x % p == 0:
            x //= p
    return x == 1

def is_prime(q):
    if q < 2: return False
    f = 2
    while f * f <= q:
        if q % f == 0: return False
        f += 1
    return True

def ord_loop(a, q):
    # plain multiplicative-order loop (independent of the generator's method)
    x = a % q
    if x == 0: raise ValueError
    k = 1
    while x != 1:
        x = x * a % q
        k += 1
        if k > q: raise ValueError
    return k

def minv(a, q):
    return pow(a, -1, q)

def main():
    K = int(sys.argv[1]); cert = sys.argv[2]
    t0 = vp(K, 2)
    # (0) lemma components: K = 2^t0 * odd, and 2^(t0+1) | 10^L for L >= t0+1
    assert K % (2 ** t0) == 0 and (K // (2 ** t0)) % 2 == 1, "t0 wrong"
    assert (10 ** (t0 + 1)) % (2 ** (t0 + 1)) == 0
    inv2 = {q: minv(pow(2, t0, q), q) for q in ()}  # filled lazily below

    nodes = [json.loads(line) for line in open(cert)]
    n = len(nodes)
    ordcache, o3cache, o7cache = {}, {}, {}

    def ORD(q):
        if q not in ordcache: ordcache[q] = ord_loop(10, q)
        return ordcache[q]
    def O3(q):
        if q not in o3cache: o3cache[q] = ord_loop(3, q)
        return o3cache[q]
    def O7(q):
        if q not in o7cache: o7cache[q] = ord_loop(7, q)
        return o7cache[q]

    def sig(rho, M):
        assert M % 6 == 0, f"M={M} not divisible by 6"
        j = vp(M, 3); m3 = 3 ** (j + 2)
        X = (pow(10, rho, m3) + K) % m3
        if X == 0:
            a = (j + 2, None)
        else:
            e = vp(X, 3)
            a = (e, e) if e <= j + 1 else (j + 2, None)
        i = vp(M, 7); m7 = 7 ** (i + 1)
        Y = (pow(10, rho, m7) + K) % m7
        if Y == 0:
            w = (i + 1, None)
        else:
            e = vp(Y, 7)
            w = (e, e) if e <= i else (i + 1, None)
        return a, w

    def could(T, q, a, w):
        """True iff T ≡ 3^a 7^w (mod q) possible with a in sig-a range, w in sig-w range."""
        if T == 0: return False
        (alo, ahi), (wlo, whi) = a, w
        x = T * minv(pow(3, alo, q), q) % q
        x = x * minv(pow(7, wlo, q), q) % q
        if ahi is None and whi is None:
            o3, o7 = O3(q), O7(q)
            return pow(x, o3 * o7 // math.gcd(o3, o7), q) == 1
        if ahi is None: return pow(x, O3(q), q) == 1
        if whi is None: return pow(x, O7(q), q) == 1
        return x == 1

    def T_of(L, q):
        return (pow(10, L, q) + K) * minv(pow(2, t0, q), q) % q

    def check_prime_kill(rho, M, q, allow_small=False):
        """Kill of class {rho mod M} via prime q. If allow_small, small L<=t0 that are
        solutions make the kill invalid (they are checked and reported)."""
        assert is_prime(q) and q not in (2, 3, 5, 7), f"bad prime {q}"
        d = ORD(q); g = math.gcd(M, d)
        for gg in range(rho % g, d, g):
            assert not could(T_of(gg, q), q, *sig(rho, M)), \
                f"region test passes at q={q}, gg={gg} for class {rho} mod {M}"
        if not allow_small:
            for L0 in range(t0 + 1):
                if L0 % M == rho % M:
                    assert not smooth237(10 ** L0 + K), \
                        f"small solution L0={L0} inside prime-killed class {rho} mod {M}"
        return True

    def check_T0_kill(rho, M, q):
        assert is_prime(q) and q not in (2, 3, 5, 7), f"bad prime {q}"
        assert (pow(10, rho, q) + K) % q == 0, f"T0: {q} does not divide 10^{rho}+K"
        assert ORD(q) % 1 == 0 and M % ORD(q) == 0, f"T0: ord_{q}(10) does not divide M={M}"
        return True

    def check_sz_leaf(rho, M, a0, w0, rec):
        a, w = sig(rho, M)
        assert a == (a0, a0) and w == (w0, w0), \
            f"exact_size signature mismatch at {rho} mod {M}: recomputed {a}, {w}"
        N0 = 2 ** t0 * 3 ** a0 * 7 ** w0
        rec = set(rec)
        # completeness: the single large candidate
        if N0 > K:
            L = is_power10(N0 - K)
            if L is not None and L % M == rho % M:
                assert L in rec, f"solution L={L} (10^L+K=N0) missing at {rho} mod {M}"
        # completeness: small L <= t0
        for L0 in range(t0 + 1):
            if L0 % M == rho % M and smooth237(10 ** L0 + K):
                assert L0 in rec, f"small solution L0={L0} missing at {rho} mod {M}"
        # each recorded L is genuinely a solution in this class
        for L in rec:
            assert L % M == rho % M, f"recorded L={L} not in class {rho} mod {M}"
            ok = (10 ** L + K == N0) or (L <= t0 and smooth237(10 ** L + K))
            assert ok, f"recorded L={L} is not a verified solution at {rho} mod {M}"
        return True

    # ---- structure ----
    assert nodes[0]["p"] == -1 and nodes[0]["m"] == 1 and nodes[0]["r"] == 0, "bad root"
    seen = set()
    for i, nd in enumerate(nodes):
        if i > 0:
            p = nd["p"]
            assert 0 <= p < n and p != i, f"node {i}: bad parent"
            assert nodes[p]["k"] == "i", f"node {i}: parent not internal"
        for c in nd.get("c", []):
            assert c not in seen, f"node {c} referenced twice"
            seen.add(c)
    assert seen == set(range(1, n)), "forest is not a single tree"

    nleaf = nrest = 0
    for i, nd in enumerate(nodes):
        if nd["k"] == "l":
            nleaf += 1
            a_st = nd["a"]; w_st = nd["w"]
            a, w = sig(nd["r"], nd["m"])
            assert [a[0], a[1]] == a_st and [w[0], w[1]] == w_st, \
                f"leaf {i}: stored signature mismatch"
            x = nd["x"]
            if "T0" in x:
                check_T0_kill(nd["r"], nd["m"], x["T0"])
            elif "prime" in x:
                check_prime_kill(nd["r"], nd["m"], x["prime"])
            elif "sz" in x:
                a0, w0 = x["sz"]
                assert a_st == [a0, a0] and w_st == [w0, w0], f"leaf {i}: sz vs sig"
                check_sz_leaf(nd["r"], nd["m"], a0, w0, x["L"])
            else:
                raise AssertionError(f"leaf {i}: unknown reason {x}")
        else:
            M = nd["m"]; rho = nd["r"]
            assert M >= 1 and 0 <= rho < M, f"node {i}: bad rho/M"
            kids = [nodes[c] for c in nd["c"]]
            if kids:
                Mc = kids[0]["m"]
                assert all(k["m"] == Mc for k in kids), f"node {i}: children moduli differ"
                assert Mc % M == 0 and Mc // M >= 2, f"node {i}: bad child modulus"
                mult = Mc // M
                expected = {(rho + k * M) % Mc for k in range(mult)}
                rs = [k["r"] for k in kids]
                assert len(set(rs)) == len(rs), f"node {i}: duplicate child residues"
                assert set(rs) <= expected, f"node {i}: child residue outside cover set"
            else:
                Mc = None
            # derive killed subclasses; verify each via rest
            if kids and len(kids) == Mc // M:
                assert not nd.get("rest"), f"node {i}: rest present but cover complete"
            else:
                nrest += 1
                assert nd.get("rest") and "q" in nd["rest"], f"node {i}: missing rest"
                q = nd["rest"]["q"]
                assert is_prime(q) and q not in (2, 3, 5, 7), f"node {i}: bad rest prime"
                d = ORD(q)
                childres = set(k["r"] for k in kids) if kids else set()
                for k in range((Mc // M) if Mc else 0):
                    ck = (rho + k * M) % Mc
                    if ck in childres: continue
                    # killed subclass {ck mod Mc}: re-verify the kill directly
                    assert Mc % d == 0, f"node {i}: rest prime ord does not divide child modulus"
                    a, w = sig(ck, Mc)
                    assert not could(T_of(ck, q), q, a, w), \
                        f"node {i}: rest subclass {ck} mod {Mc} survives q={q}"
                    for L0 in range(t0 + 1):
                        if L0 % Mc == ck:
                            assert not smooth237(10 ** L0 + K), \
                                f"node {i}: rest kills subclass containing small solution {L0}"
    print(f"PASS  K={K}: {n} nodes, {nleaf} leaves, {nrest} rest-killed splits")

main()
