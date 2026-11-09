# L2b brute.py — all 7-smooth n < 10^DIG with Pi(n) in TARGETS.
# c=0: n = 2^u 3^a 7^w ; c=1 (only when 5|t): n = 5*3^a*7^w (u=0, n ends in 5).
# Stdlib only, streaming. Run: bash -c 'ulimit -v 1500000; python3 -I brute.py'
import json, sys

DIG = int(sys.argv[1]) if len(sys.argv) > 1 else 200
TARGETS = {12, 14, 15, 16, 18, 21, 24, 32, 42, 81}
LIMIT = 10 ** DIG

def digit_prod(n):
    p = 1
    for ch in str(n):
        d = ord(ch) - 48
        if d == 0:
            return 0
        p *= d
        if p > 81:
            return p
    return p

def smooth_exp(n):
    e = {}
    for p in (2, 3, 5, 7):
        c = 0
        while n % p == 0:
            n //= p; c += 1
        if c: e[p] = c
    assert n == 1
    return e

hits = []
PW7 = []
x = 1
while x < LIMIT:
    PW7.append(x); x *= 7
NW = len(PW7)

# c = 0
NA = 0
p3 = 1
while p3 < LIMIT:
    NA += 1
    p3 *= 3
for a in range(NA):
    p3 = 3 ** a
    for w in range(NW):
        base = p3 * PW7[w]
        if base >= LIMIT:
            break
        n = base
        while n < LIMIT:
            p = digit_prod(n)
            if p in TARGETS and n >= 10:
                hits.append((p, n, smooth_exp(n)))
            n *= 2

# c = 1  (n = 5*3^a*7^w, ends in 5, odd)
for a in range(NA):
    p3 = 3 ** a
    for w in range(NW):
        n = 5 * p3 * PW7[w]
        if n >= LIMIT:
            break
        p = digit_prod(n)
        if p in TARGETS and n >= 10:
            hits.append((p, n, smooth_exp(n)))

hits.sort()
with open("/home/mj-kang/Documents/Dev/math/persistence-research/verification/glm/L2b/brute_hits.json", "w") as f:
    json.dump(hits, f)
by_t = {}
for p, n, e in hits:
    by_t.setdefault(p, []).append(n)
for t in sorted(by_t):
    print(f"t={t}: {len(by_t[t])} members, max digits {max(len(str(n)) for n in by_t[t])}")
print("total", len(hits))
