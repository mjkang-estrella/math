"""Lean-route exploration: how strong is the elementary root-split lower recursion
   G_n = 4 G_{n-1} + sum_{i=1}^{n-2} C(n-1,i) G_i G_{n-1-i}   (n >= 3),
seeded with exact P_1..P_k, combined with the doubling bound
   lim d^(1/n) >= (G_a / (a! 4 (a+1)))^(1/(a+1)) ?
Proof of the recursion (REVIEW.md C): pairs (L n R, L' n R') with |L| = |L'| = i and
equal letter sets and s(L)=s(L'), s(R)=s(R') give C(n-1,i) P_i P_{n-1-i}; the cross
pairs (n R, L' n) with s(R)=s(L') and (L n, n R') give 2 P_{n-1} more, disjoint since
the split sizes differ.  Exact integer test of > 1.73 at the best a.
argv: reviewer_P.json  max_n"""
import sys, json
from math import comb, factorial, log, exp

P = {int(k): int(v) for k, v in json.load(open(sys.argv[1]))["P"].items()}
NMAX = int(sys.argv[2])
fact = [1]
for i in range(1, NMAX + 1):
    fact.append(fact[-1] * i)
res = {}
for k in list(range(2, 13)) + [14, 16, 20]:
    G = {0: 1}
    for n in range(1, NMAX + 1):
        if n <= k:
            G[n] = P[n]
        else:
            G[n] = 4 * G[n - 1] + sum(comb(n - 1, i) * G[i] * G[n - 1 - i] for i in range(1, n - 1))
    best, besta = 0.0, None
    first = None
    for a in range(1, NMAX + 1):
        lb = exp((log(G[a]) - log(fact[a]) - log(4 * (a + 1))) / (a + 1))
        if lb > best:
            best, besta = lb, a
        if first is None and G[a] * 100 ** (a + 1) > 4 * (a + 1) * fact[a] * 173 ** (a + 1):
            first = a
    ratio = G[NMAX] / (G[NMAX - 1] * NMAX)
    res[k] = {"best_bound": best, "at_a": besta, "first_a_exact_gt_1.73": first,
              "growth_ratio_at_NMAX": ratio}
    print("seeds<=%2d  best doubling bound %.5f at a=%d  first exact a>1.73: %s  g_n/g_(n-1) at %d: %.5f"
          % (k, best, besta, first, NMAX, ratio), flush=True)
json.dump(res, open("outputs/elementary_recursion.json", "w"), indent=1)
