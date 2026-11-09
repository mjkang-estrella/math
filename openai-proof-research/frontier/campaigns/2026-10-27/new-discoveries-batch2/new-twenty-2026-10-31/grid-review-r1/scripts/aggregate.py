"""Aggregate grid-review-r1 enumeration outputs and print the Phi fibres for 2x2 and 3x3.

Usage: aggregate.py OUTDIR SUMMARY.json
Imports eqgrid.py from the same scripts directory by explicit path (no sys.path changes).
"""
import glob
import importlib.util
import json
import os
import sys

here = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location("eqgrid", os.path.join(here, "eqgrid.py"))
eg = importlib.util.module_from_spec(spec)
spec.loader.exec_module(eg)

outdir, summ = sys.argv[1], sys.argv[2]
rows = {}
for f in sorted(glob.glob(os.path.join(outdir, "*.json"))):
    if os.path.basename(f) in ("smoke.json", os.path.basename(summ)):
        continue
    for r in json.load(open(f)):
        if r.get("control_mckay"):
            continue
        key = (r["m"], r["n"])
        prev = rows.get(key)
        if prev is None or r.get("brute_matches_splitcir") is not None:
            r["_file"] = os.path.basename(f)
            rows[key] = {**(prev or {}), **r}
grids = sorted(rows)
bad = [k for k in grids if not rows[k]["prediction_holds"]]
brute = sorted(k for k in grids if rows[k].get("brute_matches_splitcir") is not None)
counts = {}
for k in grids:
    r = rows[k]
    counts.setdefault("%d eq / %d sub / |Aut| %d" % (r["eq_count"], r["sub_count"], r["aut_order"]), []).append("%dx%d" % k)


def cover(mm):
    ns = sorted(n for (m, n) in grids if m == mm)
    return ns


fibres = {}
for (m, n) in [(2, 2), (3, 3)]:
    adj = eg.grid(m, n)
    aut = eg.automorphisms(adj)
    subs = eg.subgroups(aut)
    fib = {}
    for H in subs:
        P = eg.orbit_partition(H, m * n)
        fib.setdefault(P, []).append(len(H))
    fibres["%dx%d" % (m, n)] = [
        {"partition_labels": list(P), "subgroup_orders": sorted(v)} for P, v in sorted(fib.items())
    ]
out = {
    "grids_checked": len(grids),
    "all_predictions_hold": not bad,
    "failures": bad,
    "brute_force_cross_checked": ["%dx%d" % k for k in brute],
    "brute_force_all_match": all(rows[k]["brute_matches_splitcir"] for k in brute),
    "aut_equals_A0_everywhere": all(rows[k]["aut_equals_A0"] for k in grids),
    "all_outputs_pass_definition_5_1": all(rows[k]["all_eq_pass_def51"] for k in grids),
    "coverage_by_m": {str(mm): cover(mm) for mm in sorted({m for (m, n) in grids})},
    "count_classes": counts,
    "phi_fibres_exceptional": fibres,
    "max_cpu_s_single_grid": max(rows[k]["cpu_s"] for k in grids),
}
json.dump(out, open(summ, "w"), indent=1)
print(json.dumps({k: v for k, v in out.items() if k not in ("coverage_by_m",)}, indent=1))
for mm, ns in out["coverage_by_m"].items():
    print("m=%s: n in %s" % (mm, ns))
