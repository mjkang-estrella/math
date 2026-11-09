# R6 case (M) MIXED: elementary constraints and residual form.
# Mixed configs: >=1 non-1 digit at position 0..2 (S_low), the rest far (c*10^q, q>=3).
# 9n = 10^L + A*10^q + K, K = 9*S_low - 1, n = 2^t * 3^(a-2) * 7^w.
# Pin: for q <= L: 2^t 3^a 7^w = 10^L + A*10^q + K == K (mod 10^q).
# Mod-8/5 conflict test: does there exist (t,a,w) with
#   2^t 3^a 7^w == K (mod 8) and == K (mod 5)?
# If not, the config is dead for ALL L,q.

import itertools, json

def residues(K):
    """all (t,a,w) small-class combos with 2^t 3^a 7^w == K mod 8 and mod 5"""
    ok = []
    # t: mod 8 needs t<=2 or t>=3 (0); mod 5 cycles with period 4 -> t in 0..7
    for t in range(8):
        for a in range(4):
            for w in range(4):
                v8 = (pow(2, t, 8) * pow(3, a, 8) * pow(7, w, 8)) % 8
                v5 = (pow(2, t, 5) * pow(3, a, 5) * pow(7, w, 5)) % 5
                if v8 == K % 8 and v5 == K % 5:
                    ok.append((t, a, w))
    return ok

# mixed S_low values per multiset (positions 0,1,2 only; c = digit value)
configs = {
    "{2,2}":   [1, 10, 100],                       # c=1 low, c=1 far
    "{2,3}":   [1, 10, 100, 2, 20, 200],           # c=1 or c=2 low
    "{2,4}":   [1, 10, 100, 3, 30, 300],           # c=1 or c=3 low
    "{3,3}":   [2, 20, 200],                       # c=2 low, c=2 far
    "{2,2,2}": [1, 10, 100, 11, 101, 110],         # one or two low
}

res = {}
for ms, sls in configs.items():
    rows = []
    for S in sls:
        K = 9 * S - 1
        r = residues(K)
        rows.append((S, K, len(r), r[:8]))
    res[ms] = rows
    print(f"== {ms}")
    for S, K, n, ex in rows:
        tag = "DEAD(all L,q)" if n == 0 else f"survives: {n} parity classes"
        print(f"   S_low={S:4d}  K={K:5d}  {tag}")
        if 0 < n <= 8:
            print(f"        e.g. (t,a,w)={ex[:3]}")

# sanity: known mixed member 14112: S_low=1, A=27 (c=3 at q=3), K=8, L=5
X = 10**5 + 27 * 10**3 + 8
t_, a_, w_ = 0, 0, 0
x = X
while x % 2 == 0: x //= 2; t_ += 1
while x % 3 == 0: x //= 3; a_ += 1
while x % 7 == 0: x //= 7; w_ += 1
print("14112 check: 10^5+27*10^3+8 =", X, "= 2^%d*3^%d*7^%d * %s" % (t_, a_, w_, x))
assert x == 1 and t_ == 5 and a_ == 4 and w_ == 2
print("pin mod 10^3:", X % 1000 == 8)

json.dump({ms: [(S, K, n) for S, K, n, _ in rows] for ms, rows in res.items()},
          open("r6_M_parity.json", "w"), indent=1)
print("saved r6_M_parity.json")
