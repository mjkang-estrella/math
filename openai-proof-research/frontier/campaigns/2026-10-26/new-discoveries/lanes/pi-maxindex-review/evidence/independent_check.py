#!/usr/bin/env python3
"""INDEPENDENT review checks, pi-maxindex-review lane. Written from scratch; not the parent script.

 A. Exhaustive small-mask verification of the coefficient facts
    c_i <= (k+1)/2 and c_i+c_j <= (k+4)/2 for ALL k-element ordered-pair masks (d<=5, k<=7).
 B. A_k + G_k < d at k=2d-5 (sufficiency) for d=3..11, 1200 general p per d
    (Dirichlet / sparse / peaked / near-uniform sampling), A exact, G high-precision.
 C. Sharpness family: ACTUAL sorted top-(2m+2) sums equal the predicted masks, m=2..60.
 D. Small-d classification: exact witnesses + sampled universal checks for d2k1, d3k2, d4k4.
 E. Brute-force verification of the d=4 closed forms A_4, G_4 (both branch maxima).
"""
from fractions import Fraction as F
from itertools import combinations
import json, random, math

rng = random.Random(20261026)
out = {}

# ---------- A. exhaustive mask coefficient facts ----------
def check_A():
    worst_hi, worst_pair, count = F(0), F(0), 0
    for d in range(1, 6):
        pairs = [(i, j) for i in range(d) for j in range(d)]
        for k in range(1, min(len(pairs), 7) + 1):
            for S in combinations(pairs, k):
                count += 1
                rowc = {i: 0 for i in range(d)}; colc = {i: 0 for i in range(d)}
                for (i, j) in S:
                    rowc[i] += 1; colc[j] += 1
                c = {i: F(rowc[i] + colc[i], 2) for i in range(d)}
                for i in range(d):
                    worst_hi = max(worst_hi, c[i] - F(k + 1, 2))
                for i, j in combinations(range(d), 2):
                    worst_pair = max(worst_pair, c[i] + c[j] - F(k + 4, 2))
    assert worst_hi <= 0 and worst_pair <= 0, (worst_hi, worst_pair)
    return {"exhaustive_masks": count, "max_excess_single": str(worst_hi),
            "max_excess_pair": str(worst_pair), "status": "PASS"}

out["A_mask_coefficients"] = check_A()

# ---------- exact top-k helpers ----------
def a_top(p, k):
    d = len(p)
    return sum(sorted(((F(p[i]) + F(p[j])) / 2 for i in range(d) for j in range(d)), reverse=True)[:k])

def g_top_w(w, k):
    D = sum(t * t for t in w)
    return F(sum(sorted((w[i] * w[j] for i in range(len(w)) for j in range(len(w))), reverse=True)[:k]), D)

# ---------- B. sufficiency at k=2d-5 ----------
def sample_w(d, kind):
    if kind == 0:  # Dirichlet-like, sometimes sparse
        w = [rng.expovariate(1.0) for _ in range(d)]
        if rng.random() < 0.4:
            keep = set(rng.sample(range(d), rng.randint(1, max(1, d // 2))))
            w = [w[i] if i in keep else 0.0 for i in range(d)]
    elif kind == 1:  # peaked
        w = [10.0] + [rng.random() ** 6 * 3 for _ in range(d - 1)]
    else:  # near uniform
        w = [1.0 + rng.uniform(-0.3, 0.3) for _ in range(d)]
    return w

viol, tested = 0, 0
for d in range(3, 12):
    k = 2 * d - 5
    for trial in range(1200):
        w = sample_w(d, trial % 3)
        s = sum(w)
        if s == 0: continue
        # exact p from rounded weights (10^-12 grid); exact a, high-precision g
        wi = [int(x * 10**12) for x in w]
        D = sum(t * t for t in wi)
        if D == 0: continue
        A = a_top([F(t * t, D) for t in wi], k)
        gv = sorted((wi[i] * wi[j] for i in range(d) for j in range(d)), reverse=True)
        G = F(sum(gv[:k]), D)
        tested += 1
        if A + G >= d:
            viol += 1; print("POTENTIAL VIOLATION d,k,A+G:", d, k, float(A + G))
assert viol == 0
out["B_sufficiency"] = {"general_p_vectors_tested": tested, "violations_at_k=2d-5": 0,
                        "method": "exact Fractions on 10^-12-grid weights; g via exact integer squares"}

# ---------- C. sharpness family, actual sorting ----------
c_ok = True
for m in range(2, 61):
    d = m + 3; r = 2 * m; D = r * r + m
    w = [r] + [1] * m + [0, 0]
    kp = 2 * m + 2
    A = a_top([F(t * t, D) for t in w], kp)
    G = g_top_w(w, kp)
    pred_A = F((2 * m + 3) * r * r + 2 * m, 2 * D)
    pred_G = F(r * r + 2 * m * r + 1, D)
    if A != pred_A or G != pred_G or A + G - d != F((m - 1) ** 2, 4 * m * m + m) or A + G <= d:
        c_ok = False; print("SHARPNESS MISMATCH", m, float(A), float(pred_A), float(G), float(pred_G))
out["C_sharpness"] = {"m": "2..60", "actual_sorted_sums_match_predicted_masks": c_ok}

# ---------- D. small-d classification ----------
D_out = {}
# d=1: only entry a_11=g_11=1, k=1: A+G=2>1
D_out["d1_h0"] = "k=1 gives A+G=2>1 exactly; h(1)=0"
# d=2: k=1: A_1+G_1=2p1<=2 for all p (exact). k=2 witness p=(4/5,1/5):
p2 = [F(4, 5), F(1, 5)]
A2 = a_top(p2, 2)                       # 4/5 + 1/2
G2 = g_top_w([2, 1], 2)                 # 4/5 + 2/5
D_out["d2"] = {"k1_universal": "2p1<=2 exact", "k2_witness": str(A2 + G2) + " > 2"}
# d=3: k=2 universal bound sampled exactly; k=3 witness p=(4/5,1/5,0)
A3 = a_top([F(4, 5), F(1, 5), F(0)], 3); G3 = g_top_w([2, 1, 0], 3)
D_out["d3"] = {"k3_witness": str(A3 + G3) + " > 3"}
# d=4: k=4 universal sampled exactly; k=5 witness p=(4/5,1/5,0,0)
A5 = a_top([F(4, 5), F(1, 5), F(0), F(0)], 5); G5 = g_top_w([2, 1, 0, 0], 5)
D_out["d4"] = {"k5_witness": str(A5 + G5) + " > 4"}
bad = 0; n = 200000
for _ in range(n):
    wi = [rng.randrange(0, 30) for _ in range(4)]
    D = sum(t * t for t in wi)
    if D == 0: continue
    p = [F(t * t, D) for t in wi]
    if a_top(p, 4) + g_top_w(wi, 4) > 4: bad += 1; print("d4k4 violation", wi)
    if a_top(p, 2) + g_top_w(wi, 2) > 3: bad += 1; print("d3k2 violation", wi)
D_out["sampled_200k_d4k4_and_d3k2_violations"] = bad
out["D_small_d"] = D_out

# ---------- E. d=4 closed forms ----------
ok = True
for _ in range(20000):
    wi = sorted((rng.randrange(0, 2500) for _ in range(4)), reverse=True)
    if sum(t * t for t in wi) == 0: continue
    D = sum(t * t for t in wi)
    p = [F(t * t, D) for t in wi]
    A4 = a_top(p, 4)
    pred = 2 * p[0] + p[1] + max(p[1], (p[0] + p[2]) / 2)
    if A4 != pred: ok = False; print("A4 MISMATCH", wi, float(A4), float(pred)); break
    G4 = g_top_w(wi, 4)
    predg = F(wi[0] ** 2 + 2 * wi[0] * wi[1] + max(wi[1] ** 2, wi[0] * wi[2]), D)
    if G4 != predg: ok = False; print("G4 MISMATCH", wi, float(G4), float(predg)); break
out["E_top4_formulas"] = {"A4": "2p1+p2+max(p2,(p1+p3)/2)", "G4": "p1+2x1x2+max(p2,x1x3)",
                          "brute_force_20000": "PASS" if ok else "FAIL"}

with open(__file__.replace(".py", ".json"), "w") as f:
    json.dump(out, f, indent=1, default=str)
print(json.dumps(out, indent=1, default=str))
