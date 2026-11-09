#!/usr/bin/env python3
"""Lawful single-shot public HTTP GET into a new empty directory, with a dated receipt.
Usage: fetch.py NAME URL   -> work/web/NAME/body, receipts/web-NAME.json.  No retry."""
import sys, os, json, hashlib, datetime, urllib.request, pathlib
ROOT = pathlib.Path(__file__).resolve().parent.parent
name, url = sys.argv[1], sys.argv[2]
d = ROOT / "work" / "web" / name
d.mkdir(parents=True, exist_ok=False)
req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (research review; single request)"})
rec = {"name": name, "url": url, "utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
    with urllib.request.urlopen(req, timeout=40) as r:
        body = r.read(30_000_000); rec.update(status=r.status, final_url=r.geturl(), content_type=r.headers.get("Content-Type"))
except urllib.error.HTTPError as e:
    body = e.read(200000); rec.update(status=e.code, error=str(e))
except Exception as e:
    body = b""; rec.update(status=None, error=repr(e))
(d / "body").write_bytes(body)
rec.update(bytes=len(body), sha256=hashlib.sha256(body).hexdigest())
(ROOT / "receipts" / f"web-{name}.json").write_text(json.dumps(rec, indent=1))
print(json.dumps(rec))
