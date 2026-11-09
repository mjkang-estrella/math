# Lawful single-shot HTTP fetch with dated receipt. Usage: python3 -I fetch.py URL OUTPATH
import sys, urllib.request, hashlib, json, datetime
url, out = sys.argv[1], sys.argv[2]
rec = {"url": url, "utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
    req = urllib.request.Request(url, headers={"User-Agent": "bsymbol-review-r1 (research; mailto not provided)"})
    with urllib.request.urlopen(req, timeout=60) as r:
        data = r.read(); rec["status"] = r.status; rec["final_url"] = r.geturl()
    open(out, "wb").write(data)
    rec["sha256"] = hashlib.sha256(data).hexdigest(); rec["bytes"] = len(data)
except Exception as e:
    rec["error"] = repr(e); rec["status"] = getattr(e, "code", None)
json.dump(rec, open(out + ".receipt.json", "w"), indent=1)
print(json.dumps(rec))
