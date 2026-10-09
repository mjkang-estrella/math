"""Fetch MathDB public listing for importance tiers landmark/celebrated (read-only API).
Usage: python -I analysis_mathdb_fetch.py OUTDIR"""
import json, sys, time, urllib.request
out = sys.argv[1]
for imp in ["landmark", "celebrated"]:
    items, off = [], 0
    while True:
        url = f"https://mathdb.com/api/posts?importance={imp}&limit=100&offset={off}"
        req = urllib.request.Request(url, headers={"User-Agent": "openai-proof-research-scout/0.1 (read-only)"})
        d = json.load(urllib.request.urlopen(req, timeout=60))
        got = d.get("items", [])
        items += got
        if len(got) < 100: break
        off += 100; time.sleep(0.5)
    json.dump({"retrieved": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()), "importance": imp, "items": items},
              open(f"{out}/{imp}.json", "w"), indent=1, ensure_ascii=False)
    print(imp, len(items))
