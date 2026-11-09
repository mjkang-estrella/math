# r6 v2_A.py — landscape for (A): all non-1 digits at positions <= 2.
# Part 1: enumerate the 19 (S,K) constants; sanity checks.
# Part 2: brute force L <= 3000: 7-smooth 10^L + K.
# Part 3: per K: t0, ell (mod 3), r (mod 6), regime.
# Part 4: auxiliary-prime kill (T1/T2) with CRT refinement; surviving classes.
# Run: bash -c 'ulimit -v 3000000; python3 -I v2_A.py'

import math, json
from itertools import permutations

def v2(x):
    t = 0
    while x % 2 == 0: x //= 2; t += 1
    return t

def smooth27(x):
    t = u = w = 0
    while x % 2 == 0: x //= 2; t += 1
    while x % 3 == 0: x //= 3; u += 1
    while x % 7 == 0: x //= 7; w += 1
    return t, u, w, x

def ordmod(a, m):
    x = a % m; k = 1
    while x != 1:
        x = x * a % m; k += 1
        if k > m: raise ValueError
    return k

# ---------- Part 1: constants ----------
print("== Part 1: the constants ==")
msets = {"{2,2}": [1,1], "{2,3}": [1,2], "{2,4}": [1,3], "{3,3}": [2,2], "{2,2,2}": [1,1,1]}
seen = set(); consts = []
for name, cv in msets.items():
    for perm in sorted(set(permutations(cv))):
        for pos in permutations(range(3), len(cv)):
            key = (name, tuple(sorted(zip(perm, pos))))
            if key in seen: continue
            seen.add(key)
            S = sum(c * 10**p for c, p in zip(perm, pos))
            consts.append(dict(name=name, cv=perm, pos=pos, S=S, K=9 * S - 1))
print(f"  {len(consts)} constants")
for c in consts:
    assert c["K"] == 9 * c["S"] - 1 and c["K"] % 9 == 8 and c["K"] % 5 != 0
print("  all K = 9S-1, K ≡ -1 mod 9, 5 ∤ K: PASS")

# ---------- Part 2: brute force ----------
print("== Part 2: brute force L <= 3000 ==")
LB = 3000
sols = {}
for c in consts:
    K = c["K"]; found = []
    x = 1
    for L in range(1, LB + 1):
        x *= 10
        t, u, w, cof = smooth27(x + K)
        if cof == 1:
            found.append((L, t, u, w))
    sols[K] = found
    if found:
        print(f"  K={K:>5} ({c['name']} pos={c['pos']} cv={c['cv']}): {found}")
print("  K with solutions:", [c["K"] for c in consts if sols[c["K"]]])

# ---------- Part 3: classes ----------
print("== Part 3: t0, ell, r, regime ==")
for c in consts:
    K = c["K"]
    t0 = v2(K)
    ell = (-(K + 1) // 9) % 3
    if K % 7 == 0:
        r = None
    else:
        r = next(L % 6 for L in range(6) if (pow(10, L, 7) + K) % 7 == 0)
    bad = (r is not None) and (ell % 3 == r % 3)
    c.update(t0=t0, ell=ell, r=r, bad=bad)
    print(f"  K={K:>5}: t0={t0} ell={ell} r={r} {'BAD' if bad else 'good/void'}")

# ---------- Part 4: auxiliary-prime kill ----------
print("== Part 4: auxiliary-prime kill (T1/T2), L > t0 ==")
PRIMES = []
sieve = [True] * 5000
for i in range(2, 5000):
    if sieve[i]:
        PRIMES.append(i)
        for j in range(2 * i, 5000, i): sieve[j] = False
PRIMES = [q for q in PRIMES if q not in (2, 3, 5, 7)]

report = {}
for c in consts:
    K = c["K"]; t0 = c["t0"]; ell = c["ell"]
    # classes: list of (residue, modulus, a2flag) where a2flag=True means the class
    # forces a = 2 (L ≢ ell mod 3); a2flag=False means a >= 3 possible (T1 only).
    # Seed with modulus 3: L ≡ ell -> a>=3; L ≡ ell±1 -> a=2.
    classes = [(ell % 3, 3, False), ((ell + 1) % 3, 3, True), ((ell + 2) % 3, 3, True)]
    killed_all = False; used = 0; stop_reason = ""
    for q in PRIMES:
        d = ordmod(10, q)
        o3 = ordmod(3, q); o7 = ordmod(7, q)
        e1 = o3 * o7 // math.gcd(o3, o7)
        m = pow(2, -t0, q); inv9 = pow(9, -1, q)
        G1 = set(); G2 = set()
        for rho in range(d):
            T = (pow(10, rho, q) + K) % q * m % q
            if pow(T, e1, q) == 1: G1.add(rho)
            if pow(T * inv9 % q, o7, q) == 1: G2.add(rho)
        newM = math.lcm(classes[0][1], d)
        newclasses = set()
        for rho, M, a2 in classes:
            gmod = math.gcd(M, d)
            step = d // gmod
            if step > 0 and (math.gcd(M // gmod, step) != 1):
                raise AssertionError("M//gmod not invertible")
            base_inv = pow(M // gmod, -1, step) if step > 1 else 0
            for g in (G2 if a2 else G1):
                if (g - rho) % gmod: continue
                j0 = ((g - rho) // gmod * base_inv) % step if step > 1 else 0
                for j in range(j0, newM // M, step):
                    nc = (rho + M * j) % newM
                    na2 = a2
                    if newM % 3 == 0:
                        na2 = (nc % 3) != (ell % 3)
                    # re-check condition exactly for this class
                    T = (pow(10, nc % d, q) + K) % q * m % q
                    if na2:
                        if pow(T * inv9 % q, o7, q) != 1: continue
                    else:
                        if pow(T, e1, q) != 1: continue
                    newclasses.add((nc, newM, na2))
        classes = sorted(newclasses)
        used += 1
        if not classes:
            killed_all = True; stop_reason = f"killed by q={q}"; break
        if len(classes) > 50000:
            stop_reason = "too many survivors"; break
        if classes[0][1] > 10**7:
            stop_reason = "modulus cap"; break
    mod0 = classes[0][1] if classes else 0
    print(f"  K={K:>5}: killed_all={killed_all} survivors={len(classes)} mod={mod0} primes={used} {stop_reason}")
    if classes and mod0 <= 200000:
        print(f"     surviving (L mod {mod0}): {[(r, 'a2' if a2 else 'a3') for r, M, a2 in classes][:60]}")
    report[str(K)] = dict(killed_all=killed_all, n=len(classes), mod=mod0,
                          classes=[[r, M, a2] for r, M, a2 in classes[:200]])
json.dump(report, open("r6_A_kill_report.json", "w"), indent=1)
print("saved r6_A_kill_report.json")
