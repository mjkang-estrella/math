"""Aggregate exhaustive-run JSON summaries (lane pdtar-review-r1)."""
import json, sys
agg = {}
for st, files in (("4,4", ["exh-4-4-f7-c0-64", "exh-4-4-f7-c64-128"]),
                  ("3,5", ["exh-3-5-f7-c0-64", "exh-3-5-f7-c64-96", "exh-3-5-f7-c96-128"]),
                  ("3,4", ["exh-3-4"]), ("4,3", ["exh-4-3-c0", "exh-4-3-c1"]), ("3,3", ["exh-3-3"])):
    tot = {}; fails = {}; cov = 0; ex = []
    for f in files:
        t = open(sys.argv[1] + "/" + f + ".log").read()
        j = json.loads(t[t.index("\n{") + 1:] if not t.startswith("{") else t)
        cov += j["graphs_covered"]
        for k, v in j["totals"].items(): tot[k] = tot.get(k, 0) + v
        for k, v in j["failures"].items(): fails[k] = fails.get(k, 0) + v
        ex += j["H2_but_not_K_examples"]
    agg[st] = {"graphs_covered": cov, "totals": tot, "failures": fails, "H2_not_K_examples": ex[:3]}
print(json.dumps(agg, indent=1))
