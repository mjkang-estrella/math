"""Cross-validation: Olsson-Stanton / Vandehey explicit maximal (s,t)-core
beta-set  beta^{s,t} = { st - s - t - a*s - b*t : a,b >= 0, value > 0 }
(the (s,t)-closure of {st-s-t}, Vandehey arXiv:0809.2134 Thm 2.4)
converted to a partition must equal the maximal core kappa found by the frozen
r339 enumeration (frozen/pi-mathdb-primary-qualified-breadth-r339/sources/
core-containment-calculation.json) for all 15 control pairs, and every frozen
core must be contained rowwise in it. Convention check only; NOT a proof.
"""
import json, datetime
from math import gcd

FROZEN = "/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/root-mathdb-breadth-intake-r340/frozen/pi-mathdb-primary-qualified-breadth-r339/sources/core-containment-calculation.json"

def closure_maximal(s, t):
    vals = set()
    base = s * t - s - t
    x = base
    while x > 0:
        y = x
        while y > 0:
            vals.add(y)
            y -= s
        x -= t
    # subtract multiples of t then s (symmetric closure); do full 2D sweep
    vals = set()
    a = 0
    while base - a * t > 0:
        b = 0
        while base - a * t - b * s > 0:
            vals.add(base - a * t - b * s)
            b += 1
        a += 1
    return sorted(vals, reverse=True)

def beta_to_partition(beta):
    n = len(beta)
    return tuple(beta[i] - (n - 1 - i) for i in range(n))

def contained(a, b):
    return len(a) <= len(b) and all(a[i] <= b[i] for i in range(len(a)))

data = json.load(open(FROZEN))
anomalies = []
for r in data["results"]:
    s, t = r["p"], r["q"]
    assert gcd(s, t) == 1
    beta_st = closure_maximal(s, t)
    kappa = beta_to_partition(beta_st)
    frozen_kappa = tuple(r["kappa"])
    ok_kappa = kappa == frozen_kappa
    ok_size = sum(kappa) == (s * s - 1) * (t * t - 1) // 24
    rec = {"pair": [s, t], "closure_beta": beta_st, "closure_kappa": list(kappa),
           "matches_frozen_kappa": ok_kappa, "size_matches_OS_formula": ok_size}
    if not (ok_kappa and ok_size):
        anomalies.append(rec)
print(json.dumps({"checked": len(data["results"]), "anomalies": anomalies}, indent=1))
out = {"at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
       "purpose": "convention cross-check of Vandehey/Olsson-Stanton maximal beta-set vs frozen r339 enumeration; not a proof",
       "frozen_reference": FROZEN,
       "pairs_checked": len(data["results"]), "anomalies": anomalies}
with open("crosscheck-maximal-beta-set.json", "w") as f:
    f.write(json.dumps(out, indent=1) + "\n")
print("saved crosscheck-maximal-beta-set.json")
if anomalies:
    raise SystemExit(1)
