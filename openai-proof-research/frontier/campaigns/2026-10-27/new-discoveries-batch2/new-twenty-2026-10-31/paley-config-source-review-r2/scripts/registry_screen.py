"""Path-keyword screen of cached complete trees and compare deltas. Usage: python3 -I registry_screen.py OUT.json TREE_OR_COMPARE.json..."""
import json, re, sys, hashlib
pat = re.compile(r'paley|peisert|yip|cyclotom|clique|subfield|power.?resid|shifted.?subfield|v3.?config|configuration|pappus|desargues|fano|monochrom|ramsey|line.?colo|mutually|bishop|kuss|peet|9_3|asgarli', re.I)
out = {"pattern": pat.pattern, "inputs": {}}
for f in sys.argv[2:]:
    b = open(f, "rb").read(); d = json.loads(b)
    if "tree" in d: paths = [e["path"] for e in d["tree"]]; meta = {"sha": d.get("sha"), "truncated": d.get("truncated")}
    else: paths = [x["filename"] for x in d.get("files", [])]; meta = {"status": d.get("status"), "ahead_by": d.get("ahead_by"), "total_commits": d.get("total_commits"), "n_files": len(paths), "files_capped_at_300": len(paths) >= 300}
    out["inputs"][f] = dict(meta, sha256=hashlib.sha256(b).hexdigest(), n_paths=len(paths), hits=[p for p in paths if pat.search(p)])
json.dump(out, open(sys.argv[1], "w"), indent=1)
for f, v in out["inputs"].items(): print(f, v["n_paths"], "hits:", len(v["hits"])); [print("   ", h) for h in v["hits"][:60]]
