"""FINAL-REVIEW independent math verification for Davis Conjecture 3.1.

Written from scratch (sparse dict polynomials over Fraction; independent of the
candidate's certificate.py / check_moments.py code paths). Checks:
A. Literal source P_d, q_d, R_d = P_{d+1} - q_d P_d; remainder-ratio moment identity.
B. Detailed-balance stationarity (incl. zero-weight boundary).
C. 2M + B V = (d/2) a^2, B = 4Da - D + 2a^2 - 2a; E[u]=d/2; M >= V^2 (exact).
E. Strict endpoint inequality at the exact real threshold, d=5..120 (mpmath 60 dps).
F. Tail certificate N(d,a) identity + positivity structure, exact.
G. Independent 912-coefficient finite certificates d=5..42 + cross-check vs certificates.json.
"""
from fractions import Fraction as Q
from math import comb, factorial, isqrt
import json

fails = []
def check(name, cond):
    print(("ok: " if cond else "FAIL: ") + name)
    if not cond: fails.append(name)

# ---------- sparse poly helpers ----------
def padd(p, q):
    r = dict(p)
    for e, c in q.items(): r[e] = r.get(e, Q(0)) + c
    return {e: c for e, c in r.items() if c != 0}
def pmul(p, q):
    r = {}
    for e1, c1 in p.items():
        for e2, c2 in q.items(): r[e1+e2] = r.get(e1+e2, Q(0)) + c1*c2
    return {e: c for e, c in r.items() if c != 0}
def pscale(p, c): return {e: c*v for e, v in p.items() if c*v != 0}
def falling_poly(n):
    r = {0: Q(1)}
    for k in range(n): r = pmul(r, {0: Q(-k), 1: Q(1)})
    return r
def P_poly(d):
    r = {}
    for i in range(d+1):
        r = padd(r, pscale(pmul(pmul(falling_poly(i), falling_poly(i)),
                                pmul(falling_poly(d-i), falling_poly(d-i))),
                           Q(1, factorial(i)*factorial(d-i))))
    return r
def q_poly(d): return {2: Q(2, d+1), 1: Q(-2*d, d+1), 0: Q(d, 2)}
def weights(d, x):
    f = [Q(1)]
    for i in range(d): f.append(f[-1]*(x-i))
    return [f[i]**2 * f[d-i]**2 / Q(factorial(i)*factorial(d-i)) for i in range(d+1)]

# ---------- A/B ----------
print("== A/B: remainder-ratio moment identity (exact polynomial identity) ==")
for d in [5, 6, 7, 8, 9, 10, 12, 15, 20, 25, 30, 40, 43, 50, 77]:
    Pd, Pd1 = P_poly(d), P_poly(d+1)
    R = padd(Pd1, pscale(pmul(q_poly(d), Pd), Q(-1)))
    Z, Nu, D = {}, {}, Q(d, 2)
    for i in range(d+1):
        w = pscale(pmul(pmul(falling_poly(i), falling_poly(i)),
                        pmul(falling_poly(d-i), falling_poly(d-i))),
                   Q(1, factorial(i)*factorial(d-i)))
        Z = padd(Z, w); Nu = padd(Nu, pscale(w, (Q(i)-D)**2))
    lhs = padd(pscale(pmul(R, Z), Q(2*(d+1))),
               pscale(pmul(padd(pscale(Z, Q(d)), pscale(Nu, Q(-4))), Pd), Q(1)))
    check(f"d={d}", lhs == {})

print("== B: stationarity lambda_i w_i = mu_{i+1} w_{i+1} ==")
ok = True
for d in [5, 8, 13, 21, 34, 42]:
    for x in [Q(11, 3), Q(7, 2), Q(20), Q(101, 2)]:
        w = weights(d, x)
        for i in range(d):
            if (d-i)*(x-i)**2*w[i] != (i+1)*(x-d+i+1)**2*w[i+1]:
                ok = False; print("stationarity FAIL", d, x, i)
check("stationarity (incl. integer-x zero weights, boundaries)", ok)

print("== C: 2M + B V = D a^2, E[u]=D, M>=V^2 (exact fractions) ==")
ok = True
for d in [5, 6, 7, 9, 11, 14, 18, 23, 30, 41, 42, 43, 60]:
    D = Q(d, 2)
    for a in [Q(3, 2), Q(2), Q(5, 2), Q(10), Q(51, 2), Q(200)]:
        x = D + a; w = weights(d, x); Zs = sum(w)
        V = sum(w[i]*(i-D)**2 for i in range(d+1)) / Zs
        M = sum(w[i]*(i-D)**4 for i in range(d+1)) / Zs
        B = 4*D*a - D + 2*a*a - 2*a
        if 2*M + B*V != D*a*a: ok = False; print("C FAIL", d, a)
        if sum(w[i]*i for i in range(d+1)) / Zs != D: ok = False; print("E[u] FAIL", d, a)
        if M < V*V: ok = False; print("M>=V^2 FAIL", d, a)
check("moment identity + mean + fourth-moment bound", ok)

print("== E: strict endpoint inequality (mpmath, 60 dps) ==")
import mpmath as mp
mp.mp.dps = 60
def Pval(d, x):
    fs = [mp.mpf(1)]
    for i in range(d): fs.append(fs[-1]*(x-i))
    return sum(fs[i]**2 * fs[d-i]**2 / mp.factorial(i) / mp.factorial(d-i) for i in range(d+1))
def RoverP(d, x):
    q = 2*x**2/(d+1) - 2*d*x/(d+1) + mp.mpf(d)/2
    return -(Pval(d+1, x) - q*Pval(d, x))/Pval(d, x)
ok = True; worst = mp.mpf(1)
for d in range(5, 121):
    x = (mp.mpf(d) + mp.sqrt(d+2))/2
    m = RoverP(d, x) - mp.mpf(199)/200*(d-2)/(2*x+d-2)
    if m <= 0: ok = False; print("E FAIL", d, m)
    worst = min(worst, m)
for d in [5, 9, 20, 43, 100, 300]:
    for t in [mp.mpf(0), mp.mpf('0.5'), mp.mpf(3), mp.mpf(50), mp.mpf(1000)]:
        x = (mp.mpf(d) + mp.sqrt(d+2))/2 + t
        if RoverP(d, x) <= mp.mpf(199)/200*(d-2)/(2*x+d-2):
            ok = False; print("E-beyond FAIL", d, t)
check(f"strict endpoint d=5..120 at threshold + beyond-samples (worst margin {mp.nstr(worst,4)})", ok)

print("== F: tail certificate N(d,a) ==")
ok = True
for d in [43, 44, 50, 77, 100, 500, 5000]:
    K = d*d - d + 398
    L = 400*(2*d**4 - 105*d**3 + 902*d**2 - 1197*d + 1194)
    for a in [Q(7, 4), Q(11, 2), Q(100), Q(10000, 3)]:
        T = Q(200*d*a + d*d - d + 398, 800*(a + d - 1))
        D = Q(d, 2); B = 4*D*a - D + 2*a*a - 2*a
        lhs = Q(320000)*(a + d - 1)**2 * (2*T*T + B*T - D*a*a)
        N = 800*K*(a + 2*d - 2)*(a*a - Q(d+2, 4)) + a*L + K*(201*d*d + 599*d - 402)
        if lhs != N: ok = False; print("F identity FAIL", d, a)
check("320000(a+d-1)^2(2T^2+BT-Da^2) == N exact", ok)
check("L(d)>0 d=43..199", all(400*(2*d**4-105*d**3+902*d**2-1197*d+1194) > 0 for d in range(43, 200)))
def Lshift(t): return 800*t**4+95600*t**3+3818000*t**2+51998400*t+42755200
check("claimed shift expansion of L exact",
      all(400*(2*d**4-105*d**3+902*d**2-1197*d+1194) == Lshift(d-43) for d in range(43, 120)))
import mpmath as mp2
ok = True
for d in range(43, 300):
    a = mp2.sqrt(d+2)/2
    if not (2*d*a - d/2 + 2*a*a - 2*a > 0 and 200*d*a + d*d - d + 398 > 0):
        ok = False; print("BT sign FAIL", d)
check("B>0, T>0 on domain d=43..299", ok)

print("== G: independent finite certificates d=5..42 ==")
def ipadd(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]
def ipscale(a, c): return [c*v for v in a]
def ipmul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b): r[i+j] += x*y
    return r
def ipdiv_monic(a, b):
    assert b[-1] == 1
    r = a[:]; q = [0]*(len(a)-len(b)+1)
    for i in range(len(q)-1, -1, -1):
        q[i] = r[i+len(b)-1]
        for j, v in enumerate(b): r[i+j] -= q[i]*v
    assert all(v == 0 for v in r), "division not exact"
    return q
def ifall(n):
    r = [1]
    for k in range(n): r = ipmul(r, [-k, 1])
    return r
def iS(d):
    r = [0]
    for i in range(d+1):
        r = ipadd(r, ipscale(ipmul(ipmul(ifall(i), ifall(i)),
                                   ipmul(ifall(d-i), ifall(d-i))), comb(d, i)))
    return r
def taylor_shift_frac(a, s):
    b = [Q(v) for v in a]; n = len(b)
    for i in range(n-1):
        for j in range(n-2, i-1, -1): b[j] += s*b[j+1]
    return b
total = 0; all_ok = True; per_d = {}
for d in range(5, 43):
    Sd, Sd1 = iS(d), iS(d+1)
    twoxm = [d-2, 2]
    inner = [d*(d+1)//2, -2*d, 2]
    br1 = ipadd(ipscale(ipmul(twoxm, inner), 200), ipscale([1], -199*(d+1)*(d-2)))
    H = ipadd(ipmul(br1, Sd), ipscale(ipmul(twoxm, Sd1), -200))
    F = ipmul(ifall((d+1)//2), ifall((d+1)//2))
    G = ipdiv_monic(H, F)
    while len(G) > 1 and G[-1] == 0: G.pop()
    m = 1000*d + isqrt(1000000*(d+2))
    k = m - 1000*d
    assert k >= 0 and k*k <= 1000000*(d+2), f"r_d > threshold at d={d}"
    Gs = taylor_shift_frac(G, Q(m, 2000))
    Ndeg = len(Gs)-1
    scaled = [c * Q(2000)**Ndeg for c in Gs]
    pos = all(c.denominator == 1 and c > 0 for c in scaled)
    if not pos: all_ok = False; print("G FAIL d=", d, [str(c) for c in scaled][:4])
    total += len(scaled); per_d[d] = [int(c) for c in scaled]
check(f"all 38 shifted certificates all-positive integers (total coeffs {total}; claimed 912)",
      all_ok and total == 912)

print("== G2: cross-check against certificates.json ==")
C = json.load(open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/parent-davis/certificates.json'))
rows = {r['d']: r for r in C}
matched = 0; mism = []
for d, coeffs in per_d.items():
    r = rows.get(d)
    theirs = r['shifted_scaled_coefficients'] if r else None
    if theirs == coeffs: matched += 1
    else: mism.append(d)
print(f"shifted coefficient lists matching certificates.json: {matched}/38; mismatches: {mism}")
receipt = json.load(open('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-26/new-discoveries/lanes/parent-davis/certificate-receipt.json'))
print("receipt:", {k: receipt[k] for k in ('cases','all_coefficients_strictly_positive','coefficient_count')})

print()
print("RESULT:", "ALL PASS" if not fails else f"FAILURES: {fails}")
