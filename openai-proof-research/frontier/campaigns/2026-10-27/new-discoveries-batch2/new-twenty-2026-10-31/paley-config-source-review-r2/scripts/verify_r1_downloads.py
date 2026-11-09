"""Verify r1 downloaded bytes against r1 logs/http-receipts.jsonl (last receipt per file wins). Usage: python3 -I verify_r1_downloads.py R1DIR OUT.json"""
import hashlib, json, os, sys
r1 = sys.argv[1]; last = {}
for l in open(os.path.join(r1, "logs/http-receipts.jsonl")):
    d = json.loads(l); last[d["file"]] = d
res = {}
for f, d in last.items():
    p = os.path.join(r1, f)
    got = hashlib.sha256(open(p, "rb").read()).hexdigest() if os.path.exists(p) else None
    res[f] = {"url": d["url"], "status": d["status"], "receipt_utc": d["utc"], "receipt_sha256": d["sha256"], "actual_sha256": got, "match": got == d["sha256"]}
json.dump(res, open(sys.argv[2], "w"), indent=1)
print(sum(v["match"] for v in res.values()), "of", len(res), "match")
for f, v in res.items():
    if not v["match"]: print("MISMATCH", f)
