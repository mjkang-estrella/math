"""Single-attempt public HTTP GET with dated receipts. No retries.
Usage: python3 -I fetch.py OUTFILE URL [OUTFILE URL ...]; receipts appended to logs/http-receipts.jsonl (relative to cwd)."""
import sys, json, hashlib, datetime, urllib.request, urllib.error, os
args = sys.argv[1:]
for out, url in zip(args[0::2], args[1::2]):
    rec = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "url": url, "file": out}
    try:
        req = urllib.request.Request(url, headers={"User-Agent": "research-review/1.0 (bounded single-attempt; mailto withheld)", "Accept": "*/*"})
        with urllib.request.urlopen(req, timeout=40) as r:
            b = r.read(); rec.update(status=r.status, final_url=r.geturl(), content_type=r.headers.get("Content-Type"), bytes=len(b), sha256=hashlib.sha256(b).hexdigest())
            os.makedirs(os.path.dirname(out) or ".", exist_ok=True); open(out, "wb").write(b)
    except urllib.error.HTTPError as e:
        rec.update(status=e.code, error=str(e))
    except Exception as e:
        rec.update(status="error", error=repr(e))
    open("logs/http-receipts.jsonl", "a").write(json.dumps(rec) + "\n")
    print(rec.get("status"), rec.get("bytes"), url)
