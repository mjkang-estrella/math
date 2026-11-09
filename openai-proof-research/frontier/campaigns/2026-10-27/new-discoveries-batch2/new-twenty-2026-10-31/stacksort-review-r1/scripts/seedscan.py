"""Resumed-run script (written 2026-11-03 after the HTTP 500 interruption).
Adversarial 'routine-ness' scan: with only the brute-force-range seeds P_1..P_k
(Defant, Troupes Remark 7.30: brute force stops near n = 14), does the elementary
root-split lower recursion
    G_n = 4 G_{n-1} + sum_{i=1}^{n-2} C(n-1,i) G_i G_{n-1-i}    (n > k),  G_n = P_n (n <= k)
plus the doubling bound (G_a / (a! 4 (a+1)))^(1/(a+1)) ever exceed 1.73 (and 1.8)?
Normalised floats: g_n = G_n/n! satisfies g_n = (4 g_{n-1} + sum g_i g_{n-1-i}) / n;
scaled h_n = g_n / gam^n to avoid overflow.  FLOAT SCAN ONLY: any crossing found here is
re-checked with exact integers by scripts/seedexact.py.
argv: reviewer_P.json  NMAX  k1,k2,...
"""
import sys, json, math
from operator import mul

P = {int(k): int(v) for k, v in json.load(open(sys.argv[1]))["P"].items()}
NMAX = int(sys.argv[2])
KS = [int(x) for x in sys.argv[3].split(",")]
GAM = 1.75
LG = math.log(GAM)
out = {}
for k in KS:
    h = [1.0]
    fact = 1
    for n in range(1, k + 1):
        fact *= n
        h.append(math.exp(math.log(P[n]) - math.log(fact) - n * LG))
    for n in range(k + 1, NMAX + 1):
        seg = h[1:n - 1]
        conv = sum(map(mul, seg, reversed(seg)))
        h.append((4 * h[n - 1] + conv) / (n * GAM))
    first = {}
    best = (0.0, None)
    for a in range(1, NMAX + 1):
        lg = math.log(h[a]) + a * LG          # log g_a
        b = math.exp((lg - math.log(4 * (a + 1))) / (a + 1))
        if b > best[0]:
            best = (b, a)
        for thr in (1.73, 1.8):
            if thr not in first and b > thr:
                first[thr] = a
    growth = h[NMAX] / h[NMAX - 1] * GAM      # g_N / g_{N-1}
    out[k] = {"first_a_float_gt_1.73": first.get(1.73), "first_a_float_gt_1.8": first.get(1.8),
              "best": best[0], "best_a": best[1], "g_ratio_at_NMAX": growth}
    print("seeds<=%2d  first a(>1.73)=%s  first a(>1.8)=%s  best %.5f at a=%s  g_N/g_N-1=%.5f"
          % (k, first.get(1.73), first.get(1.8), best[0], best[1], growth), flush=True)
json.dump({"NMAX": NMAX, "results": out}, open("outputs/seedscan.json", "w"), indent=1)
