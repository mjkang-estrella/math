import json, hashlib, sys, os, datetime
fz = json.load(open(sys.argv[1]))
out = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "frozenUtc": fz["utc"], "checked": 0, "match": 0, "mismatch": [], "missing": []}
for p, h in fz["files"].items():
    out["checked"] += 1
    if not os.path.exists(p):
        out["missing"].append(p); continue
    hh = hashlib.sha256(open(p, 'rb').read()).hexdigest()
    if hh == h: out["match"] += 1
    else: out["mismatch"].append({"path": p, "expected": h, "actual": hh})
json.dump(out, open(sys.argv[2], 'w'), indent=1)
print(out["checked"], out["match"], len(out["mismatch"]), len(out["missing"]))
