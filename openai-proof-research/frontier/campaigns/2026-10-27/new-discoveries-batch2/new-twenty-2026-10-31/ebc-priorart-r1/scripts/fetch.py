"""Single-URL fetcher for the ebc-priorart-r1 lane.

Usage: python3 -I fetch.py URL OUTDIR LABEL
- TLS verification left at the default (verified); never disabled.
- Redirects are NOT followed automatically; a 3xx is recorded with its Location.
- OUTDIR must not exist yet (fresh empty directory per download).
- Appends one JSON line to receipts/network.jsonl next to this script's lane.
"""
import sys, os, json, hashlib, datetime, urllib.request, urllib.error, ssl

url, outdir, label = sys.argv[1], sys.argv[2], sys.argv[3]
lane = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.makedirs(outdir, exist_ok=False)

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        return None

ctx = ssl.create_default_context()
opener = urllib.request.build_opener(NoRedirect, urllib.request.HTTPSHandler(context=ctx))
req = urllib.request.Request(url, headers={"User-Agent": "Mozilla/5.0 (X11; Linux x86_64) research-priorart-check/1.0", "Accept": "*/*"})
utc = datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")
status, body, headers, err = None, b"", {}, None
try:
    with opener.open(req, timeout=40) as r:
        status = r.status
        headers = dict(r.headers)
        body = r.read(30_000_000)
except urllib.error.HTTPError as e:
    status = e.code
    headers = dict(e.headers or {})
    try:
        body = e.read(2_000_000)
    except Exception:
        body = b""
except Exception as e:
    err = repr(e)
ct = headers.get("Content-Type", "")
ext = ".pdf" if body[:5] == b"%PDF-" else (".json" if "json" in ct else (".html" if "html" in ct else ".bin"))
fn = os.path.join(outdir, "body" + ext)
with open(fn, "wb") as f:
    f.write(body)
rec = {"label": label, "utc": utc, "url": url, "status": status, "error": err,
       "content_type": ct, "location": headers.get("Location"), "bytes": len(body),
       "file": os.path.relpath(fn, lane), "sha256": hashlib.sha256(body).hexdigest()}
with open(os.path.join(lane, "receipts", "network.jsonl"), "a") as f:
    f.write(json.dumps(rec) + "\n")
print(json.dumps(rec, indent=1))
