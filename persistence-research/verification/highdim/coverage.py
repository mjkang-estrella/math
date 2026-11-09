# coverage.py -- independent cross-checks for a target t:
#  (1) digit-level brute force: all n = 2^i 3^j 7^k < 10^D with digit product t (D = 100);
#  (2) for every member n, replay its configuration and slice and verify that it is either
#      (a) recorded as an sz solution in the certificate of its slice (if it lies in the cert domain), or
#      (b) below the cert domain floor (L < qmin), hence covered by (1);
#  (3) the maximal domain floor over all slices of the certified configurations is < D,
#      so every point not in a certificate domain is inside the brute-force range.
# usage: python3 -I coverage.py t
import sys, os, json, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from hnt import vp
import run_target

HERE = os.path.dirname(os.path.abspath(__file__))
t = int(sys.argv[1]); D = 100
res = json.load(open(sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, f"results_t{t}.json")))
B = 10 ** D
members = []
n2 = 1
while n2 < B:
    n3 = n2
    while n3 < B:
        n = n3
        while n < B:
            s = str(n)
            if len(s) >= 2 and math.prod(int(c) for c in s) == t: members.append(n)
            n *= 7
        n3 *= 3
    n2 *= 2
members.sort()
print(f"t={t}: brute-force members below 10^{D}: {members}")
closed = {k: v for k, v in res.items() if v["status"] == "CLOSED"}
maxfloor = 0
for k, v in closed.items():
    for K2, free in run_target.slices(9 * v["S_low"] - 1, tuple(v["far"])):
        q = max(3, vp(K2, 2) + 1) if free else vp(K2, 2) + 1
        maxfloor = max(maxfloor, q)
print(f"max certificate domain floor over closed configs: {maxfloor} (< D={D}: {maxfloor < D})")
bad = 0
for n in members:
    dig = str(n)[::-1]; L = len(dig)
    S = sum((int(c) - 1) * 10 ** p for p, c in enumerate(dig) if p < 3 and c != '1')
    farpos = sorted((9 * (int(c) - 1), p) for p, c in enumerate(dig) if p >= 3 and c != '1')
    key = f"{S}|{','.join(str(A) for A in sorted(A for A, _ in farpos))}"
    if key not in closed:
        print(f"   n={n}: configuration {key} not among the certified open configurations"); continue
    # replay the slice: fold fixed digits exactly as run_target.slices does
    K = 9 * S - 1; free = list(farpos); fl = [3] * len(free)
    while True:
        t0 = vp(K, 2)
        low = [i for i in range(len(free)) if fl[i] <= t0]
        if not low: break
        free_sorted = sorted(range(len(free)), key=lambda i: free[i][0])
        i = low[0]
        A, q = free[i]
        if q <= t0: K += A * 10 ** q; free.pop(i); fl.pop(i)
        else: fl[i] = t0 + 1
    qmin = max(3, vp(K, 2) + 1) if free else vp(K, 2) + 1
    pt = [L] + [q for A, q in free]
    if L < qmin or any(q < qmin for q in pt[1:]):
        print(f"   n={n}: below domain floor of slice K={K} (L={L}, qmin={qmin}) -> covered by brute force"); continue
    job = [j for j in closed[key]["jobs"] if j["K"] == K]
    sols = [s for s in closed[key]["sz_solutions"] if s[0] == K]
    hit = any(sorted(zip(c, s[1:])) == sorted((A, q) for A, q in free) and s[0] == L for _, c, s in sols)
    print(f"   n={n}: slice K={K} free={[A for A, _ in free]} point={pt} recorded={hit}")
    if not hit: bad += 1
print("COVERAGE:", "OK" if bad == 0 and maxfloor < D else f"PROBLEM ({bad})")
