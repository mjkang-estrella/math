"""Resumed-run script (2026-11-03).  Exact-integer confirmation of seedscan.py crossings and
re-check of the certificates from the r133 lane table and the reviewer table.

Part A (P tables, n <= 82; integer tests only):
  doubling  (d_a/(4(a+1)))^(1/(a+1)) > p/q  <=>  P_a q^(a+1) > 4 (a+1) a! p^(a+1)
  sup       (d_{n-1}/n^2)^(1/n)      > p/q  <=>  P_{n-1} q^n > n^2 (n-1)! p^n
  for thresholds 173/100 (Conjecture 4.4, v3/v4) and 9/5 (v1/v2 remark "(1.6, 1.8)").
Part B (elementary recursion with exact seeds P_1..P_k, exact integers):
  G_n = 4 G_{n-1} + sum_{i=1}^{n-2} C(n-1,i) G_i G_{n-1-i}; first a with the doubling test.
argv: lane_table.json reviewer_P.json  k:AMAX[:thr] ...   (thr in {173/100, 9/5})
"""
import sys, json
from math import factorial
from fractions import Fraction

lane = {int(k): int(v) for k, v in json.load(open(sys.argv[1])).items()}
rev = {int(k): int(v) for k, v in json.load(open(sys.argv[2]))["P"].items()}
assert lane == rev and set(lane) == set(range(1, 83))
P = rev
print("lane table == reviewer table for n = 1..82:", lane == rev)


def dbl(Pa, a, p, q, fa):
    return Pa * q ** (a + 1) > 4 * (a + 1) * fa * p ** (a + 1)


fac = [1]
for i in range(1, 2001):
    fac.append(fac[-1] * i)

print("certificate 1  P_50*100^51 > 4*51*50!*173^51 :",
      P[50] * 100 ** 51 > 4 * 51 * factorial(50) * 173 ** 51)
print("certificate 2  P_78*100^79 > 79^2*78!*173^79 :",
      P[78] * 100 ** 79 > 79 ** 2 * factorial(78) * 173 ** 79)
resA = {}
for (p, q) in ((173, 100), (9, 5)):
    da = [a for a in range(1, 83) if dbl(P[a], a, p, q, fac[a])]
    sp = [n for n in range(2, 84) if P[n - 1] * q ** n > n * n * fac[n - 1] * p ** n]
    key = "%d/%d" % (p, q)
    resA[key] = {"doubling_a": da[:1] + (["... %d" % da[-1]] if da else []),
                 "doubling_all_from_first": bool(da) and da == list(range(da[0], 83)),
                 "sup_n": sp[:1] + (["... %d" % sp[-1]] if sp else [])}
    print("threshold", key, "doubling holds for a:", resA[key]["doubling_a"],
          "contiguous:", resA[key]["doubling_all_from_first"], "| sup holds for n:", resA[key]["sup_n"])

resB = {}
for spec in sys.argv[3:]:
    parts = spec.split(":")
    k, AMAX = int(parts[0]), int(parts[1])
    p, q = (9, 5) if len(parts) > 2 and parts[2] == "9/5" else (173, 100)
    G = [1] + [P[n] for n in range(1, k + 1)]
    row = [1]  # C(n-1, .) for current n; start with n-1 = 0
    for n in range(1, AMAX + 1):
        if n >= 2:
            row = [1] + [row[i] + row[i + 1] for i in range(len(row) - 1)] + [1]  # C(n-1, .)
        if n > k:
            s = 4 * G[n - 1]
            for i in range(1, n - 1):
                s += row[i] * G[i] * G[n - 1 - i]
            G.append(s)
    first = None
    hold = []
    pq, qq = p, q
    for a in range(1, AMAX + 1):
        ok = G[a] * q ** (a + 1) > 4 * (a + 1) * fac[a] * p ** (a + 1)
        if ok and first is None:
            first = a
        hold.append(ok)
    tail_ok = first is not None and all(hold[first - 1:])
    # sanity: G_n <= P_n where both known
    le = all(G[n] <= P[n] for n in range(1, min(AMAX, 82) + 1))
    resB[spec] = {"first_a": first, "holds_for_all_a_from_first_to_AMAX": tail_ok,
                  "G_le_P_n_le_82": le, "threshold": "%d/%d" % (p, q),
                  "bits_G_AMAX": G[AMAX].bit_length()}
    print("seeds<=%d  threshold %d/%d  exact first a = %s  (holds through a=%d: %s)  G<=P(n<=82): %s"
          % (k, p, q, first, AMAX, tail_ok, le), flush=True)
json.dump({"A": resA, "B": resB}, open("outputs/seedexact.json", "w"), indent=1)
