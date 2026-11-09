#!/usr/bin/env python3
"""Fetch ONE URL into a fresh empty directory (reviewer lane rlmexc-review-r1).

Usage: python3 -I fetch1.py URL OUTDIR FILENAME RECEIPTS_JSONL

* TLS verification stays ON (default ssl context).  No retries.
* Redirects are followed only within the same host; a cross-host redirect is
  recorded and NOT followed.
* OUTDIR must not exist yet (fresh empty directory); it is created here.
* A receipt line (utc, url, final url, status, bytes, sha256, error) is appended.
"""
import datetime
import hashlib
import json
import os
import sys
import urllib.error
import urllib.parse
import urllib.request

UA = "rlmexc-review-r1/1.0 (python-urllib; research review fetch)"


class SameHostRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        old = urllib.parse.urlsplit(req.full_url).hostname
        new = urllib.parse.urlsplit(newurl).hostname
        if old != new:
            raise urllib.error.HTTPError(newurl, code, "cross-host redirect refused: %s -> %s" % (old, new), headers, fp)
        return super().redirect_request(req, fp, code, msg, headers, newurl)


def main():
    url, outdir, fname, receipts = sys.argv[1:5]
    os.makedirs(outdir, exist_ok=False)
    rec = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(), "url": url,
           "file": os.path.join(outdir, fname)}
    opener = urllib.request.build_opener(SameHostRedirect())
    req = urllib.request.Request(url, headers={"User-Agent": UA, "Accept": "*/*"})
    try:
        with opener.open(req, timeout=60) as r:
            data = r.read(30_000_000)
            rec.update(status=r.status, final_url=r.geturl(), bytes=len(data),
                       sha256=hashlib.sha256(data).hexdigest(),
                       content_type=r.headers.get("Content-Type"))
            with open(rec["file"], "wb") as f:
                f.write(data)
    except urllib.error.HTTPError as e:
        rec.update(status=e.code, error=str(e.reason))
    except Exception as e:  # network / TLS errors are recorded, never bypassed
        rec.update(status=None, error="%s: %s" % (type(e).__name__, e))
    with open(receipts, "a") as f:
        f.write(json.dumps(rec, sort_keys=True) + "\n")
    print(json.dumps(rec, sort_keys=True))


if __name__ == "__main__":
    main()
