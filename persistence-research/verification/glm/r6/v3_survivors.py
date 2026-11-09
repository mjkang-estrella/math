# r6 v3_survivors.py — stronger kill for (A) constants.
# Class refinement over L mod M with:
#   - lambda ladder: a >= k  <=>  L ≡ lambda_k (mod 3^(k-2)), k >= 3  (a = v3(10^L+K))
#   - mu ladder:     w >= k  <=>  L ≡ mu_k (mod 6*7^(k-1)), k >= 1  (w = v7(10^L+K))
#   - aux-prime tests: 9n = 2^t0 3^a 7^w => T := (10^L+K)*2^(-t0) ≡ 3^a 7^w (mod q)
#     membership via order tests (x^o3==1 etc.). Exact a / w derived from class modulus.
# Strategy: greedily apply the aux prime with the best kill rate; when none kills,
# deepen the 3-adic (x3) or 7-adic (x7) class modulus to make more exponents exact.
# Run: bash -c 'ulimit -v 3000000; python3 -I v3_survivors.py'

import math, json, sys
from collections import defaultdict
from itertools import permutations

def v2(x):
    t = 0
    while x % 2 == 0: x //= 2; t += 1
    return t

def ordmod(a, m):
    x = a % m; k = 1
    while x != 1:
        x = x * a % m; k += 1
        if k > m: raise ValueError(f"ord undefined a={a} m={m}")
    return k

def lambda_ladder(K, kmax):
    lam = {}
    sols = [x for x in range(1, 4) if (pow(10, x, 27) + K) % 27 == 0]
    assert len(sols) == 1, (K, sols)
    lam[3] = sols[0]
    for k in range(3, kmax):
        step = 3 ** (k - 2); base = lam[k]; found = None
        for j in range(3):
            x = base + j * step
            if (pow(10, x, 3 ** (k + 1)) + K) % 3 ** (k + 1) == 0:
                found = x; break
        assert found is not None, (K, k)
        lam[k + 1] = found
    return lam

def mu_ladder(K, kmax):
    if K % 7 == 0: return None
    mu = {}
    sols = [x for x in range(1, 7) if (pow(10, x, 7) + K) % 7 == 0]
    assert len(sols) == 1
    mu[1] = sols[0]
    for k in range(1, kmax):
        step = 6 * 7 ** (k - 1); base = mu[k]; found = None
        for j in range(7):
            x = base + j * step
            if (pow(10, x, 7 ** (k + 1)) + K) % 7 ** (k + 1) == 0:
                found = x; break
        assert found is not None, (K, k)
        mu[k + 1] = found
    return mu

def a_range(rho, M, lam, Jcap=26):
    J = 0
    while J < Jcap and M % (3 ** (J + 1)) == 0: J += 1
    k = 2
    while k + 1 <= J + 2 and (rho - lam[k + 1]) % (3 ** (k - 1)) == 0:
        k += 1
    return (k, None) if k + 1 > J + 2 else (k, k)

def w_range(rho, M, mu, Icap=10):
    if mu is None: return (0, 0)
    I = 0
    while I < Icap and M % (6 * 7 ** (I + 1)) == 0: I += 1
    k = 0
    while k + 1 <= I + 1 and (rho - mu[k + 1]) % (6 * 7 ** k) == 0:
        k += 1
    return (k, None) if k + 1 > I + 1 else (k, k)

def prime_list(bound):
    sieve = [True] * bound; ps = []
    for i in range(2, bound):
        if sieve[i]:
            ps.append(i)
            for j in range(2 * i, bound, i): sieve[j] = False
    return ps

PRIMES = [q for q in prime_list(20000) if q not in (2, 3, 5, 7)]
# order by ord_q(10) ascending: cheapest, strongest constraints first
try:
    PRIMES.sort(key=lambda q: ordmod(10, q) if math.gcd(q, 10) == 1 else 10 ** 9)
except Exception:
    pass

def region_pass(q, T, sig, cache):
    """T ≡ 3^a 7^w (mod q) for some a,w in ranges? sig=(a_lo,a_hi,w_lo,w_hi)."""
    if T == 0: return False
    key = (q, sig)
    e = cache.get(key)
    if e is None:
        a_lo, a_hi, w_lo, w_hi = sig
        o3 = ordmod(3, q); o7 = ordmod(7, q)
        if a_hi is None and w_hi is None: e = o3 * o7 // math.gcd(o3, o7)
        elif a_hi is None: e = o3
        elif w_hi is None: e = o7
        else: e = 0
        cache[key] = e
    a_lo, a_hi, w_lo, w_hi = sig
    x = T * pow(3, -a_lo, q) % q * pow(7, -w_lo, q) % q
    if e == 0: return x == 1
    return pow(x, e, q) == 1

def refine_K(K, t0, lam, mu, prime_cap=150, qbound=20000,
             maxM=4 * 10**9, maxC=3_000_000, verbose=False):
    M = 6
    classes = set(range(6))
    cache = {}
    used = []
    applied = set()
    history = []
    round_no = 0
    while True:
        if not classes:
            return dict(status="CLOSED", M=M, used=used, history=history)
        round_no += 1
        sigs = defaultdict(list)
        for rho in classes:
            sigs[(a_range(rho, M, lam) + w_range(rho, M, mu))].append(rho)
        # scan unapplied primes (ascending d) for best kill
        best = None
        scanned = 0
        for q in PRIMES:
            if q in applied or q > qbound: continue
            try:
                d = ordmod(10, q)
            except ValueError:
                continue
            m = pow(2, -t0, q)
            g = math.gcd(M, d)
            killed = 0; total = 0
            for sig, rhos in sigs.items():
                gset = [gg for gg in range(d)
                        if region_pass(q, (pow(10, gg, q) + K) % q * m % q, sig, cache)]
                gm = {gg % g for gg in gset}
                killed += sum(1 for rho in rhos if rho % g not in gm)
                total += len(rhos)
            frac = killed / total if total else 0
            if best is None or frac > best[0]:
                best = (frac, q, d)
            scanned += 1
            if scanned >= 40: break
        if best and best[0] > 0.005:
            frac, q, d = best
            applied.add(q)
            g = math.gcd(M, d); newM = M * d // g
            m = pow(2, -t0, q)
            newclasses = set()
            for sig, rhos in sigs.items():
                gset = [gg for gg in range(d)
                        if region_pass(q, (pow(10, gg, q) + K) % q * m % q, sig, cache)]
                if not gset: continue
                gm = defaultdict(list)
                for gg in gset: gm[gg % g].append(gg)
                step = d // g
                invMg = pow(M // g, -1, step) if step > 1 else 0
                for rho in rhos:
                    for gg in gm.get(rho % g, ()):
                        j = ((gg - rho) // g * invMg) % step
                        nc = (rho + M * j) % newM
                        a_lo, a_hi = a_range(nc, newM, lam)
                        w_lo, w_hi = w_range(nc, newM, mu)
                        T = (pow(10, nc % d, q) + K) % q * m % q
                        if region_pass(q, T, (a_lo, a_hi, w_lo, w_hi), cache):
                            newclasses.add(nc)
            classes = newclasses; M = newM
            used.append((q, round(frac, 3)))
            history.append(("P", q, len(classes), M))
            continue
        # no prime killed enough -> deepen
        if M * 3 <= maxM and len(classes) * 3 <= maxC:
            newM = M * 3
            classes = {(rho + M * j) % newM for rho in classes for j in range(3)}
            M = newM
            history.append(("D3", None, len(classes), M))
            continue
        if M * 7 <= maxM and len(classes) * 7 <= maxC:
            newM = M * 7
            classes = {(rho + M * j) % newM for rho in classes for j in range(7)}
            M = newM
            history.append(("D7", None, len(classes), M))
            continue
        return dict(status="OPEN", M=M, used=used, history=history,
                    classes=sorted(classes)[:3000000], nclasses=len(classes),
                    note="no progress; caps or prime cap", rounds=round_no)

# ---------- constants ----------
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

# known true solutions (L <= 3000 brute force) that MUST survive as classes:
KNOWN = {188: [2, 6], 116: [2], 278: [2]}

if __name__ == "__main__":
    out = {}
    for c in consts:
        K = c["K"]; t0 = v2(K)
        lam = lambda_ladder(K, 27)
        mu = mu_ladder(K, 12)
        res = refine_K(K, t0, lam, mu)
        st = res["status"]
        msg = f"K={K:>5} ({c['name']} pos={c['pos']}): {st}"
        if st == "CLOSED":
            msg += f"  (final M={res['M']}, primes used={len(res['used'])})"
        else:
            msg += f"  survivors={res.get('nclasses')} mod M={res['M']}"
            # sanity: known solutions must survive
            if K in KNOWN:
                cls = set(res["classes"])
                full = res.get("nclasses", 0) <= 2000
                for L in KNOWN[K]:
                    ok = any((L - cc) % res["M"] == 0 for cc in cls) if full else "skip"
                    msg += f" [L={L} survives: {ok}]"
                    assert ok is not False, f"KNOWN SOLUTION L={L} KILLED for K={K}!"
        print(msg, flush=True)
        out[str(K)] = {k: (v if k != "classes" else list(v)) for k, v in res.items()}
    json.dump(out, open("r6_v3_out.json", "w"), default=str)
    print("saved r6_v3_out.json")
