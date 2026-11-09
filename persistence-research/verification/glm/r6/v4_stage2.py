# r6 v4_stage2.py — close K=188 and K=278 (or produce the precise residual).
# Extends v3: endless refinement rounds; per round:
#   - rescan ALL primes <= qbound with current (a,w)-ranges (regions shift as
#     the class modulus gains 3- and 7-adic depth); apply best kill.
#   - if no prime kills: deepen 3-adic (x3) or 7-adic (x7), alternating.
#   - size-kill: if a and w both EXACT for a class (a0, w0), then
#       a0*ln3 + w0*ln7 in [L*ln10 - t0*ln2, L*ln10 - t0*ln2 + delta_max]
#     pins L to an interval of width delta_max/ln10 + 1; L ≡ rho (mod M) then
#     leaves <= a handful of concrete L (all small) -> verify by exact
#     7-smoothness test of 10^L + K; keep class only if a true solution lies
#     in it (and record that L).
# Run: bash -c 'ulimit -v 3000000; python3 -I v4_stage2.py'

import math, json
from collections import defaultdict
import importlib.util, os
_spec = importlib.util.spec_from_file_location(
    "v3_survivors", os.path.join(os.path.dirname(os.path.abspath(__file__)), "v3_survivors.py"))
_v3 = importlib.util.module_from_spec(_spec); _spec.loader.exec_module(_v3)
v2, ordmod = _v3.v2, _v3.ordmod
lambda_ladder, mu_ladder = _v3.lambda_ladder, _v3.mu_ladder
a_range, w_range = _v3.a_range, _v3.w_range
prime_list, refine_K = _v3.prime_list, _v3.refine_K
consts, KNOWN, PRIMES = _v3.consts, _v3.KNOWN, _v3.PRIMES

LN3, LN7, LN10, LN2 = math.log(3), math.log(7), math.log(10), math.log(2)

def smooth27(x):
    t = u = w = 0
    while x % 2 == 0: x //= 2; t += 1
    while x % 3 == 0: x //= 3; u += 1
    while x % 7 == 0: x //= 7; w += 1
    return t, u, w, x

def region_pass(q, T, sig, cache):
    if T == 0: return False
    e = cache.get((q, sig))
    if e is None:
        a_lo, a_hi, w_lo, w_hi = sig
        o3 = ordmod(3, q); o7 = ordmod(7, q)
        if a_hi is None and w_hi is None: e = o3 * o7 // math.gcd(o3, o7)
        elif a_hi is None: e = o3
        elif w_hi is None: e = o7
        else: e = 0
        cache[(q, sig)] = e
    a_lo, a_hi, w_lo, w_hi = sig
    x = T * pow(3, -a_lo, q) % q * pow(7, -w_lo, q) % q
    return x == 1 if e == 0 else pow(x, e, q) == 1

def build_prime_order(qbound):
    rows = []
    for q in PRIMES:
        if q > qbound: break
        try:
            d = ordmod(10, q); o3 = ordmod(3, q); o7 = ordmod(7, q)
        except ValueError:
            continue
        dens = o3 * o7 // math.gcd(o3, o7) / (q - 1)
        rows.append((dens, q))
    rows.sort()
    return [q for _, q in rows]

def stage2(K, t0, lam, mu, init=None, rounds=150, qbound=50000, maxM=10**17, maxC=20_000_000):
    if init is None:
        M = 6; classes = set(range(6))
    else:
        M = init['M']; classes = set(init['classes'])
    cache = {}
    gsetcache = {}
    used = []
    hist = []
    true_sols = []   # verified (L, a, w) kept from size-kill
    deep3 = True
    PORD = build_prime_order(qbound)
    for rnd in range(rounds):
        if not classes:
            for L in (KNOWN.get(K) or []):
                if L <= t0: continue
                assert any(vs[0] == L for vs in true_sols), f"L={L} lost at CLOSED"
            return dict(status="CLOSED", M=M, used=used, hist=hist, true_sols=true_sols)
        J = 0
        while M % (3 ** (J + 1)) == 0: J += 1
        Imax = 0
        while M % (6 * 7 ** (Imax + 1)) == 0: Imax += 1
        sigs = defaultdict(list)
        for rho in classes:
            sigs[(a_range(rho, M, lam) + w_range(rho, M, mu))].append(rho)
        # scan primes for best kill
        best = None; scanned = 0
        for q in PORD:
            if scanned >= 300: break
            try: d = ordmod(10, q)
            except ValueError: continue
            m = pow(2, -t0, q)
            g = math.gcd(M, d)
            killed = 0; total = 0
            for sig, rhos in sigs.items():
                key = (q, sig)
                gs = gsetcache.get(key)
                if gs is None:
                    gs = [gg for gg in range(d)
                          if region_pass(q, (pow(10, gg, q) + K) % q * m % q, sig, cache)]
                    gsetcache[key] = gs
                gm = {gg % g for gg in gs}
                killed += sum(1 for rho in rhos if rho % g not in gm)
                total += len(rhos)
            frac = killed / total if total else 0
            if best is None or frac > best[0]:
                best = (frac, q, d)
            if frac > 0.9: break
            scanned += 1
        if best and best[0] > 0.002:
            frac, q, d = best
            g = math.gcd(M, d); newM = M * d // g
            m = pow(2, -t0, q)
            newclasses = set()
            for sig, rhos in sigs.items():
                gs = gsetcache.get((q, sig))
                if gs is None:
                    gs = [gg for gg in range(d)
                          if region_pass(q, (pow(10, gg, q) + K) % q * m % q, sig, cache)]
                    gsetcache[(q, sig)] = gs
                if not gs: continue
                gm = defaultdict(list)
                for gg in gs: gm[gg % g].append(gg)
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
            if newclasses and (len(newclasses) > maxC or newM > maxM):
                pass  # skip application this round
            else:
                classes = newclasses; M = newM
                used.append((q, round(frac, 3)))
                hist.append(("P", q, len(classes), M))
                continue
        # size-kill for both-exact classes
        newclasses = set()
        for rho in classes:
            a_lo, a_hi = a_range(rho, M, lam)
            w_lo, w_hi = w_range(rho, M, mu)
            if a_hi is not None and w_hi is not None:
                # exact: a0*ln3 + w0*ln7 = L*ln10 - t0*ln2 + delta,
                # delta = ln(1 + K/10^L) ∈ (0, ln(1+K/100)] for L >= 2
                a0, w0 = a_lo, w_lo
                X = a0 * LN3 + w0 * LN7 + t0 * LN2
                dmax = math.log(1 + K / 100.0)
                lo = (X - dmax) / LN10
                hi = (X + 1e-9) / LN10
                cand = []
                k0 = 0
                # L ≡ rho mod M; L in [max(1,lo), hi]
                base = rho % M
                start = max(1, int(math.ceil(lo)))
                end = int(math.floor(hi))
                k = 0
                while base + k * M <= end:
                    L = base + k * M
                    if L >= start:
                        cand.append(L)
                    k += 1
                    if k > 100: break
                for L in cand:
                    if L <= 3000:
                        t_, u_, w_, cof = smooth27(10**L + K)
                        if cof == 1:
                            true_sols.append((L, t_, u_ - 2, w_))
                # class is RESOLVED: every L in it is either one of the (verified)
                # candidates in [lo,hi] or dead by the size window. Drop it.
                continue
            newclasses.add(rho)
        if len(newclasses) != len(classes):
            hist.append(("SIZEKILL", None, len(newclasses), M))
        classes = newclasses
        if not classes:
            return dict(status="CLOSED", M=M, used=used, hist=hist, true_sols=true_sols)
        # deepen (pick side with more unbounded ranges; fall back to feasible side)
        n_ua = sum(1 for rho in classes if a_range(rho, M, lam)[1] is None)
        n_uw = sum(1 for rho in classes if w_range(rho, M, mu)[1] is None)
        want3 = n_ua >= n_uw
        can3 = M * 3 <= maxM and len(classes) * 3 <= maxC
        can7 = M * 7 <= maxM and len(classes) * 7 <= maxC
        do3 = (want3 and can3) or (not can7 and can3)
        do7 = (not want3 and can7) or (not can3 and can7)
        if do3:
            newM = M * 3
            classes = {(rho + M * j) % newM for rho in classes for j in range(3)}
            M = newM
            hist.append(("D3", None, len(classes), M))
        elif do7:
            newM = M * 7
            classes = {(rho + M * j) % newM for rho in classes for j in range(7)}
            M = newM
            hist.append(("D7", None, len(classes), M))
        else:
            break
    res = dict(status="OPEN", M=M, used=used, hist=hist, true_sols=true_sols,
               classes=sorted(classes), nclasses=len(classes))
    if K in KNOWN:
        verified = {vs[0] for vs in true_sols}
        for L in KNOWN[K]:
            if L <= t0 or L in verified: continue
            ok = any((L - cc) % M == 0 for cc in classes)
            assert ok, f"KNOWN SOLUTION L={L} KILLED for K={K}"
    return res

if __name__ == "__main__":
    out = {}
    for c in consts:
        K = c["K"]
        if K not in (188, 278): continue
        t0 = v2(K)
        lam = lambda_ladder(K, 30)
        mu = mu_ladder(K, 14)
        # stage 1 first (v3 refinement)
        r1 = refine_K(K, t0, lam, mu)
        print(f"K={K}: stage1={r1['status']} M={r1['M']} survivors={r1.get('nclasses','-')}", flush=True)
        if r1["status"] == "CLOSED":
            out[str(K)] = r1; continue
        init = dict(M=int(r1["M"]), classes=[int(x) for x in r1["classes"]])
        assert r1["nclasses"] <= len(init["classes"]), "stage-1 class list truncated"
        res = stage2(K, t0, lam, mu, init=init, rounds=300)
        print(f"K={K}: {res['status']}  M={res['M']} classes={res.get('nclasses','-')}")
        print("  P-cut trend:", [(h[1], h[2]) for h in res["hist"] if h[0] == "P"][-25:])
        print("  true_sols found:", sorted(set(res["true_sols"])))
        if res["status"] == "OPEN" and res["M"] <= 10**7:
            print("  surviving classes:", res["classes"][:50])
        # sanity: true solutions' classes must survive
        cls = set(res.get("classes", [])) if res["status"] == "OPEN" else None
        if cls is not None and res["M"] <= 10**7:
            for L in KNOWN[K]:
                ok = any((L - cc) % res["M"] == 0 for cc in cls)
                print(f"  sanity L={L} survives: {ok}")
                assert ok
        out[str(K)] = {k: v for k, v in res.items()}
    json.dump(out, open("r6_v4_out.json", "w"), default=str)
