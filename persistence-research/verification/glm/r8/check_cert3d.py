# r8 check_cert3d.py — independent checker for the 3-D two-far residual certificate
#   cert_3d_S1.jsonl: the 9 residual classes (L,q1,q2) mod M = 2*3^7*7^5 of the
#   two-far {2,2,2} S_low=1 problem, each killed by the aux-prime region test at p=37.
#
# Certified statement: there is NO (L, q1, q2) with L > q2 > q1 >= 4 and
#   2^3 * 3^a * 7^w = 10^L + 9*10^q1 + 9*10^q2 + 8        (t = v2(RHS) = 3 since q1 >= 4)
# in any of the 9 classes, because on each class a >= 9 and w >= 6 (uniform signature)
# but 3^a 7^w ≡ T (mod 37) is unsolvable for a >= 9, w >= 6.
#
# usage: python3 check_cert3d.py cert_3d_S1.jsonl
import json, math, sys

lines = [l for l in open(sys.argv[1]).read().split("\n") if l.strip()]
meta = json.loads(lines[0])
assert meta["k"] == "meta"
K, Q1MIN = meta["K"], meta["q1min"]
assert K == 8
t0 = 3
assert Q1MIN > t0, "t = t0 = 3 requires q1 >= 4"

def vp(n, p):
    c = 0
    while n % p == 0:
        n //= p; c += 1
    return c

def order(g, q):
    o = q - 1; f = 2; n = o
    while f * f <= n:
        if n % f == 0:
            while n % f == 0: n //= f
            while o % f == 0 and pow(g, o // f, q) == 1: o //= f
        f += 1
    if n > 1:
        while o % n == 0 and pow(g, o // n, q) == 1: o //= n
    return o

def fac(n):
    f = {}; p = 2
    while p * p <= n:
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f

def ord_pp(a, p, k):
    o = 1; x = a % p
    while x != 1:
        x = x * a % p; o += 1
    pk = p
    for _ in range(k - 1):
        pk *= p
        if pow(a, o, pk) != 1: o *= p
    return o

seen = set()
for line in lines[1:]:
    d = json.loads(line)
    assert d["k"] == "l"
    L, q1, q2 = d["r"]
    ML, M1, M2 = d["m"]
    assert ML == M1 == M2, "one modulus for all three coordinates"
    M = ML
    key = (L % M, q1 % M, q2 % M)
    assert key not in seen, "duplicate class"
    seen.add(key)
    # signature validity: ord_{3^9}(10) = 3^7 and ord_{7^6}(10) = 6*7^5 must divide M
    assert M % 3**7 == 0 and M % (6 * 7**5) == 0 and M % 2 == 0
    X = (pow(10, L, 3**9) + 9 * pow(10, q1, 3**9) + 9 * pow(10, q2, 3**9) + K) % 3**9
    assert X == 0, ("a-signature: RHS not ≡ 0 mod 3^9 on the whole class", d)
    Y = (pow(10, L, 7**6) + 9 * pow(10, q1, 7**6) + 9 * pow(10, q2, 7**6) + K) % 7**6
    assert Y == 0, ("w-signature: RHS not ≡ 0 mod 7^6 on the whole class", d)
    assert d["a"] == [9, None] and d["w"] == [6, None], ("leaf signature mismatch", d)
    # kill: aux prime region test, t = t0 = 3
    p = d["x"]["prime"]
    assert p not in (2, 3, 5, 7)
    dd = order(10, p)
    g = math.gcd(M, dd)
    inv2 = pow(pow(2, t0, p), -1, p)
    o3, o7 = order(3, p), order(7, p)
    e = o3 * o7 // math.gcd(o3, o7)
    for ggL in range(L % g, dd, g):
        for gg1 in range(q1 % g, dd, g):
            for gg2 in range(q2 % g, dd, g):
                T = (pow(10, ggL, p) + 9 * pow(10, gg1, p) + 9 * pow(10, gg2, p) + K) * inv2 % p
                if T == 0:
                    continue  # T ≡ 0 would also kill (p | RHS), but cannot happen here
                x = T * pow(pow(3, 9, p), -1, p) % p
                x = x * pow(pow(7, 6, p), -1, p) % p
                # reachable set {3^a 7^w : a>=9, w>=6} = 3^9 7^6 <3,7>; kill iff x ∉ <3,7>
                assert pow(x, e, p) != 1, ("region kill fails", d, ggL, gg1, gg2)
n = len(lines) - 1
print(f"two-far S_low=1 residual: {n} classes mod M, all killed by the p=37 region test "
      f"(a >= 9, w >= 6 uniform; T*3^-9*7^-6 outside <3,7> mod 37)  -> CERTIFICATE VALID")
