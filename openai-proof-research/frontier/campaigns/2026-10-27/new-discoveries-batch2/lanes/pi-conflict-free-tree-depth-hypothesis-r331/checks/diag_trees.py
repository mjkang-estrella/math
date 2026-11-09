#!/usr/bin/env python3
"""Diagnostics: slack distribution D vs 2*max(Delta, ceil(log2 n));
tight trees (slack<=2); D-Delta vs log2(n/Delta) pattern; deeper n."""
import json, os, sys, math, datetime
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from scan_trees import enumerate_unlabeled, canon, D_of, max_delta

def main():
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 18
    start = int(sys.argv[2]) if len(sys.argv) > 2 else 2
    reps = enumerate_unlabeled(N)
    out = {"N": N, "start": start,
           "generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
           "slack_min_by_n": {}, "tight_examples": [], "pattern_violations": [],
           "max_DDelt_minus_logratio": None}
    gmax = None
    for n in range(max(2, start), N + 1):
        smin = None; tight = []
        for edges in reps[n]:
            D = D_of(n, edges)
            Delta = max_delta(n, edges)
            L = (n - 1).bit_length()
            slack = 2 * max(Delta, L) - D
            if smin is None or slack < smin:
                smin = slack
            if slack <= 2 and n >= 10:
                tight.append({"canon": canon(n, edges), "D": D, "Delta": Delta,
                              "L": L, "slack": slack, "edges": [list(e) for e in edges]})
            # pattern: D - Delta vs log2(n/Delta)
            val = (D - Delta) - math.log2(n / Delta)
            if gmax is None or val > gmax[0]:
                gmax = (val, n, D, Delta, canon(n, edges))
            if D > Delta + L - 1:
                out["pattern_violations"].append(
                    {"canon": canon(n, edges), "D": D, "Delta": Delta, "L": L,
                     "edges": [list(e) for e in edges]})
        out["slack_min_by_n"][n] = smin
        out["tight_examples"].extend(tight)
        print(f"n={n}: min slack={smin}, tight={len(tight)}, pattern_viol={len(out['pattern_violations'])}", flush=True)
    out["max_(D-Delta)-log2(n/Delta)"] = gmax
    print(json.dumps({k: out[k] for k in ["slack_min_by_n", "max_(D-Delta)-log2(n/Delta)"]}, indent=1, default=str))
    print("pattern violations (D > Delta+L-1):", len(out["pattern_violations"]))
    print("tight examples:", json.dumps(out["tight_examples"][:12], indent=1))
    W = os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), "work")
    os.makedirs(W, exist_ok=True)
    with open(os.path.join(W, f"diag-{start}-{N}.json"), "w") as f:
        json.dump(out, f, indent=1)
    print("DONE", datetime.datetime.now(datetime.timezone.utc).isoformat())

if __name__ == "__main__":
    main()
