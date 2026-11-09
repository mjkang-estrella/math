#!/usr/bin/env python3
"""Collect watchdog receipts of the reviewer's Lean builds/checks into outputs/lean-runs-summary.json."""
import json, glob, os
B = os.path.join(os.path.dirname(__file__), "..", "lean-build", "logs"); out = {}
for f in sorted(glob.glob(os.path.join(B, "*.watch.json"))):
    d = json.load(open(f)); k = os.path.basename(f)[:-len(".watch.json")]
    out[k] = {x: d[x] for x in ("rc", "wall_s", "cpu_s", "peak_private_rss_MiB", "peak_total_rss_MiB", "killed", "utc_end")}
mx = max(out.values(), key=lambda v: v["peak_private_rss_MiB"])
json.dump({"runs": out, "num_runs": len(out), "max_peak_private_rss_MiB": mx["peak_private_rss_MiB"],
           "max_cpu_s": max(v["cpu_s"] for v in out.values()), "max_wall_s": max(v["wall_s"] for v in out.values()),
           "any_killed": any(v["killed"] for v in out.values())},
          open(os.path.join(B, "..", "..", "outputs", "lean-runs-summary.json"), "w"), indent=1)
for k, v in out.items(): print(k, v["rc"], v["cpu_s"], v["peak_private_rss_MiB"])
