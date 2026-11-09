# r7 verify_against_brute.py — soundness cross-check of the certificates.
# 1. Walks the partition tree for every L in [0, LMAX] and asserts:
#      leaf killed (prime/T0) or rest-killed  =>  10^L+K is NOT {2,3,7}-smooth
#      leaf exact_size                        =>  (L in recorded) <=> smooth
# 2. Signature soundness: for a sample of classes, check the v3/v7 bounds on
#    class members via MODULAR valuations (works for huge L too):
#      e = v_p(10^L+K) <= cap  <=>  pow(10,L,p^e) + K ≡ 0 (mod p^e) and not mod p^{e+1}.
# 3. Region-test soundness: every 3^a*7^w with (a,w) in the signature ranges
#    must pass the subgroup test (no false kills).
# Run: python3 -I verify_against_brute.py 188 cert_K188.jsonl [LMAX]

import json, math, random, sys

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

def ord_loop(a, q):
    x = a % q; k = 1
    while x != 1:
        x = x * a % q; k += 1
    return k

def vp_mod(L, p, cap, K):
    # largest e <= cap with p^e | 10^L+K (computed mod p^{cap+1})
    m = p ** (cap + 1)
    r = (pow(10, L, m) + K) % m
    if r == 0:
        return cap + 1
    e = 0
    while r % p == 0:
        r //= p; e += 1
    return e

def main():
    K = int(sys.argv[1]); cert = sys.argv[2]
    LMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
    t0 = vp(K, 2)
    nodes = [json.loads(line) for line in open(cert)]

    def walk(L):
        nd = nodes[0]
        while nd["k"] == "i":
            kids = [nodes[c] for c in nd["c"]]
            if kids:
                Mc = kids[0]["m"]
                ck = L % Mc
                nxt = [k for k in kids if k["r"] == ck]
                if nxt:
                    nd = nxt[0]; continue
            return ("rest", nd)
        return ("leaf", nd)

    nsol = 0
    for L in range(LMAX + 1):
        kind, nd = walk(L)
        s = smooth237(10 ** L + K)
        if kind == "rest":
            assert not s, f"L={L}: smooth but rest-killed"
        else:
            x = nd["x"]
            if "sz" in x:
                assert (L in x["L"]) == s, f"L={L}: exact_size membership mismatch"
            else:
                assert not s, f"L={L}: smooth but killed by {x}"
        nsol += s
    sols = [L for L in range(LMAX + 1) if smooth237(10 ** L + K)]
    print(f"tree walk L<={LMAX}: OK ({nsol} smooth); brute solutions: {sols}")

    random.seed(7)
    idxs = [i for i in range(len(nodes)) if nodes[i]["k"] == "l" and nodes[i]["m"] >= 6]
    sample = idxs if len(idxs) <= 250 else random.sample(idxs, 250)
    for i in sample:
        nd = nodes[i]
        M = nd["m"]; rho = nd["r"]
        j = vp(M, 3); i7 = vp(M, 7)
        j = min(j, 12); i7 = min(i7, 6)   # valuation cap for the test
        for k in range(6):
            L = rho + k * M
            e3 = vp_mod(L, 3, j + 2, K)
            if e3 <= j + 1:
                # stored sig must claim a = e3 exactly (if it stored exact <= j+1)
                sta, stw = nd["a"], nd["w"]
                assert not (sta[1] is not None and sta[0] != e3 and sta[0] <= j + 1), \
                    f"node {i}: stored a={sta} but true a={e3} at L={L}"
            for L2 in (L, L + M):
                e3b = vp_mod(L2, 3, j + 2, K)
                e7b = vp_mod(L2, 7, i7 + 2, K)
                # uniform bounds claimed by the node must hold
                if nd["a"][1] is not None:
                    assert e3b == nd["a"][0], f"node {i}: claimed exact a={nd['a'][0]}, true {e3b} at L={L2}"
                else:
                    assert e3b >= nd["a"][0], f"node {i}: a lower bound violated at L={L2}"
                if nd["w"][1] is not None:
                    assert e7b == nd["w"][0], f"node {i}: claimed exact w={nd['w'][0]}, true {e7b} at L={L2}"
                else:
                    assert e7b >= nd["w"][0], f"node {i}: w lower bound violated at L={L2}"
    print("signature spot checks (modular): OK")

    ordc = {}
    def ORD(a, q):
        if (a, q) not in ordc: ordc[(a, q)] = ord_loop(a, q)
        return ordc[(a, q)]

    def could(T, q, a, w):
        if T == 0: return False
        (alo, ahi), (wlo, whi) = a, w
        x = T * pow(pow(3, alo, q), -1, q) % q
        x = x * pow(pow(7, wlo, q), -1, q) % q
        if ahi is None and whi is None:
            o3, o7 = ORD(3, q), ORD(7, q)
            return pow(x, o3 * o7 // math.gcd(o3, o7), q) == 1
        if ahi is None: return pow(x, ORD(3, q), q) == 1
        if whi is None: return pow(x, ORD(7, q), q) == 1
        return x == 1

    checked = 0
    for i in sample:
        nd = nodes[i]
        a, w = nd["a"], nd["w"]
        (alo, ahi), (wlo, whi) = a, w
        ahi_t = ahi if ahi is not None else min(alo + 15, alo + ORD(3, 101) - 1)
        whi_t = whi if whi is not None else min(wlo + 15, wlo + ORD(7, 101) - 1)
        if (ahi_t - alo + 1) * (whi_t - wlo + 1) > 500: continue
        for q in (101, 331, 887):
            for aa in range(alo, ahi_t + 1):
                for ww in range(wlo, whi_t + 1):
                    T = pow(3, aa, q) * pow(7, ww, q) % q
                    assert could(T, q, a, w), f"FALSE KILL node {i} q={q} a={aa} w={ww}"
                    checked += 1
    print(f"region soundness: {checked} exponent pairs checked, OK")

main()
