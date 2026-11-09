"""Fetch one URL into a FRESH empty directory with an HTTP receipt (never overwrites).
Usage: fetch.py DOWNLOADS_ROOT RECEIPTS_DIR TAG URL
- TLS verification left at default (verified). No retries.
- Redirects: same-host redirects followed (max 3); cross-host redirects refused and recorded.
- Denied hosts (by rule) refused without contacting them."""
import sys, os, json, hashlib, datetime, urllib.request, urllib.error, urllib.parse, ssl
root, rdir, tag, url = sys.argv[1:5]
DENY = ("crossref.org", "semanticscholar.org", "export.arxiv.org/api", "arxiv.org/api", "sciencedirect.com", "dblp.org", "dblp.uni-trier.de", "elsevier.com")
ts = datetime.datetime.now(datetime.timezone.utc).strftime("%Y%m%dT%H%M%S%fZ")
d = os.path.join(root, "%s-%s" % (tag, ts)); os.makedirs(d)  # fresh, must not exist
assert not os.listdir(d)
rec = {"tag": tag, "url": url, "utc": ts, "dir": d, "redirects": []}
if any(x in url for x in DENY):
    rec["status"] = "REFUSED_DENIED_HOST"
else:
    host0 = urllib.parse.urlparse(url).hostname
    class NoCross(urllib.request.HTTPRedirectHandler):
        max_redirections = 3
        def redirect_request(self, req, fp, code, msg, headers, newurl):
            rec["redirects"].append({"code": code, "to": newurl})
            if urllib.parse.urlparse(newurl).hostname != host0:
                raise urllib.error.HTTPError(newurl, code, "cross-host redirect refused", headers, fp)
            return super().redirect_request(req, fp, code, msg, headers, newurl)
    op = urllib.request.build_opener(NoCross, urllib.request.HTTPSHandler(context=ssl.create_default_context()))
    req = urllib.request.Request(url, headers={"User-Agent": "research-review-script/1.0 (python-urllib)"})
    try:
        r = op.open(req, timeout=40)
        body = r.read(60 * 1024 * 1024)
        rec["status"] = r.status; rec["final_url"] = r.geturl()
        rec["headers"] = {k: v for k, v in r.headers.items() if k.lower() in ("content-type", "content-length", "last-modified", "etag", "date", "content-encoding", "x-ratelimit-remaining")}
        fn = os.path.join(d, "body")
        with open(fn, "xb") as f: f.write(body)
        rec["bytes"] = len(body); rec["sha256"] = hashlib.sha256(body).hexdigest(); rec["file"] = fn
    except urllib.error.HTTPError as e:
        rec["status"] = e.code; rec["error"] = str(e.reason)
    except Exception as e:
        rec["status"] = "ERROR"; rec["error"] = repr(e)
with open(os.path.join(rdir, "%s-%s.json" % (tag, ts)), "x") as f:
    json.dump(rec, f, indent=1)
print(json.dumps({k: rec.get(k) for k in ("tag", "status", "bytes", "sha256", "redirects", "error")}))
