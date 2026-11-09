"""Compare the reviewer's P_n tables (brute force, label-insertion automaton, top-max
recursion in naive and packed modes) with each other and with the r133 lane table, then
check the certificate inequalities exactly with integers.
argv: lane_table.json label_insertion_log brute.json naive.json packed.json"""
import sys, json, re
from math import factorial
from decimal import Decimal, getcontext

getcontext().prec = 60
lane_f, li_log, brute_f, naive_f, packed_f = sys.argv[1:6]
lane = {int(k): int(v) for k, v in json.load(open(lane_f)).items()}
brute = {int(k): v["P"] for k, v in json.load(open(brute_f)).items()}
naive = {int(k): int(v) for k, v in json.load(open(naive_f))["P"].items()}
packed = {int(k): int(v) for k, v in json.load(open(packed_f))["P"].items()}
li = {}
for line in open(li_log):
    m = re.fullmatch(r"(\d+) (\d+)\n", line)
    if m:
        li[int(m.group(1))] = int(m.group(2))

print("sizes lane", len(lane), "brute", len(brute), "label-insertion", len(li),
      "naive", len(naive), "packed", len(packed))
assert naive == packed, "naive != packed"
for n, v in brute.items():
    assert naive[n] == v, ("brute", n)
for n, v in li.items():
    assert naive[n] == v, ("label-insertion", n)
mism = [n for n in range(1, 83) if lane.get(n) != naive.get(n)]
print("lane table vs reviewer (n=1..82) mismatches:", mism)
assert set(lane) == set(range(1, 83))

P = naive
# Certificate 1 (doubling form): P_50 * 100^51 > 4 * 51 * 50! * 173^51
c1 = P[50] * 100 ** 51 > 4 * 51 * factorial(50) * 173 ** 51
# Certificate 2 (source sup formula): P_78 * 100^79 > 79^2 * 78! * 173^79
c2 = P[78] * 100 ** 79 > 79 ** 2 * factorial(78) * 173 ** 79
print("certificate doubling a=50:", c1)
print("certificate source-sup n=79 (uses d_78):", c2)


def root(x, k):
    return (Decimal(x).ln() / k).exp()


def dbl(a):  # (d_a / (4(a+1)))^(1/(a+1))
    return root(Decimal(P[a]) / Decimal(factorial(a)) / (4 * (a + 1)), a + 1)


def sup(n):  # (d_{n-1}/n^2)^(1/n)
    return root(Decimal(P[n - 1]) / Decimal(factorial(n - 1)) / (n * n), n)


def dbl_int(a):
    return P[a] * 100 ** (a + 1) > 4 * (a + 1) * factorial(a) * 173 ** (a + 1)


def sup_int(n):
    return P[n - 1] * 100 ** n > n * n * factorial(n - 1) * 173 ** n


# sharper doubling with log(a_{k+1}) instead of log(a_{k+1}+1) is not used; report the lane's form
first_dbl = [a for a in range(1, 83) if dbl_int(a)]
first_sup = [n for n in range(2, 84) if sup_int(n)]
print("doubling bound > 1.73 holds for a in", first_dbl[:3], "... smallest", first_dbl[0] if first_dbl else None)
print("all a >= smallest also hold:", first_dbl == list(range(first_dbl[0], 83)) if first_dbl else None)
print("source sup formula > 1.73 holds for n in", first_sup, "smallest", first_sup[0] if first_sup else None)
for a in (first_dbl[0] - 1, first_dbl[0], 50, 78, 82):
    print("doubling a=%d bound %s" % (a, str(dbl(a))[:12]))
for n in (first_sup[0] - 1, first_sup[0], 83):
    print("sup n=%d bound %s" % (n, str(sup(n))[:12]))
# ratio heuristics
for n in (40, 60, 70, 80, 82):
    print("n=%d  d_n^(1/n)=%s  d_n/d_(n-1)=%s" % (
        n, str(root(Decimal(P[n]) / Decimal(factorial(n)), n))[:8],
        str(Decimal(P[n]) / (Decimal(P[n - 1]) * n))[:8]))
# d_n >= 1 sanity (sum of squares >= sum)
assert all(P[n] >= factorial(n) for n in P)
# elementary recursion check: P_n >= 4 P_{n-1} + sum_{i=1}^{n-2} C(n-1,i) P_i P_{n-1-i}
from math import comb
assert all(P[n] >= 4 * P[n - 1] + sum(comb(n - 1, i) * P[i] * P[n - 1 - i] for i in range(1, n - 1))
           for n in range(2, 83))
print("elementary root-split inequality holds for n=2..82")
json.dump({"P": {n: str(P[n]) for n in sorted(P)}, "lane_mismatches": mism,
           "cert_doubling_a50": c1, "cert_sup_n79": c2,
           "smallest_a_doubling": first_dbl[0], "smallest_n_sup": first_sup[0],
           "doubling_bound_a50": str(dbl(50))[:20], "sup_bound_n79": str(sup(79))[:20]},
          open("outputs/reviewer_P_1_82_and_certificates.json", "w"), indent=1)
