import json, datetime
from math import comb, gcd

NMAX = 45

def gen_partitions(n, max_part=None):
    if max_part is None or max_part > n: max_part = n
    if n == 0:
        yield ()
        return
    for first in range(max_part, 0, -1):
        for rest in gen_partitions(n - first, min(first, n - first)):
            yield (first,) + rest

def beta_set(lam):
    l = len(lam)
    return set(lam[i] + l - i - 1 for i in range(l))

SMAX = 13
pair_ids = {}
for p in range(2, SMAX + 1):
    for q in range(p + 1, SMAX + 1):
        if gcd(p, q) != 1:
            continue
        kmax = (p * p - 1) * (q * q - 1) // 24
        if kmax <= NMAX:
            pair_ids[(p, q)] = kmax

cores_by_pair = {k: [] for k in pair_ids}
total = 0
for (p, q) in pair_ids:
    cores_by_pair[(p, q)].append((0, ()))  # empty partition: a core for every pair
for n in range(1, NMAX + 1):
  for lam in gen_partitions(n):
    total += 1
    b = beta_set(lam)
    ok = []
    for s in range(2, SMAX + 1):
        good = True
        for a in b:
            if a >= s and (a - s) not in b:
                good = False
                break
        if good:
            ok.append(s)
    if not ok:
        continue
    sz = sum(lam)
    for (p, q) in pair_ids:
        if p in ok and q in ok:
            cores_by_pair[(p, q)].append((sz, lam))
print("partitions scanned:", total, flush=True)

results, anomalies = [], []
for (p, q), kmax in sorted(pair_ids.items()):
    cores = cores_by_pair[(p, q)]
    count_expected = comb(p + q, p) // (p + q)
    maxcore = max(cores)[1]
    contained = lambda a, b: len(a) <= len(b) and all(a[i] <= b[i] for i in range(len(a)))
    all_in = all(contained(c[1], maxcore) for c in cores)
    r = {"p": p, "q": q, "kappa_size_expected": kmax, "max_size_found": max(cores)[0],
         "count_expected": count_expected, "count_found": len(cores),
         "count_match": len(cores) == count_expected,
         "max_size_match": max(cores)[0] == kmax,
         "all_contained": all_in, "kappa": list(maxcore)}
    results.append(r)
    if not (r["count_match"] and r["max_size_match"] and all_in):
        anomalies.append(r)

print("pairs:", len(results), "anomalies:", len(anomalies))
for r in results:
    print(f"({r['p']},{r['q']}): count {r['count_found']}/{r['count_expected']} maxsize {r['max_size_found']}/{r['kappa_size_expected']} contained {r['all_contained']}")

out = {"at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
       "nmax": NMAX, "pairs_checked": len(results), "anomalies": anomalies, "results": results}
open("core-containment-calculation.json", "w").write(json.dumps(out, indent=1) + "\n")
print("saved core-containment-calculation.json")
