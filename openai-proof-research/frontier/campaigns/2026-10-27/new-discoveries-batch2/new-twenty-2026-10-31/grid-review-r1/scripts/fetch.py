"""Polite public HTTP fetcher for lane grid-review-r1 (written for this lane).

Usage: fetch.py OUTDIR NAME=URL [NAME=URL ...]
Saves each body to OUTDIR/NAME and a receipt OUTDIR/NAME.receipt.json (url, final url, status,
bytes, sha256, utc). On HTTP 403 or 429, or a challenge page, it records the response and
skips every later URL on the same host (no retries). Sleeps 3 s between requests.
"""
import hashlib
import json
import os
import sys
import time
import urllib.error
import urllib.parse
import urllib.request

UA = "grid-review-r1 research fetcher (python-urllib; single requests, no crawling)"


def main():
    out = sys.argv[1]
    os.makedirs(out, exist_ok=True)
    blocked = set()
    for item in sys.argv[2:]:
        name, url = item.split("=", 1)
        host = urllib.parse.urlparse(url).netloc
        rec = {"name": name, "url": url, "utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())}
        if host in blocked:
            rec["status"] = "SKIPPED_HOST_BLOCKED_EARLIER"
        else:
            try:
                req = urllib.request.Request(url, headers={"User-Agent": UA})
                with urllib.request.urlopen(req, timeout=40) as r:
                    body = r.read(30_000_000)
                    rec["status"] = r.status
                    rec["final_url"] = r.geturl()
                    rec["content_type"] = r.headers.get("Content-Type")
            except urllib.error.HTTPError as e:
                body = e.read(200_000)
                rec["status"] = e.code
                if e.code in (403, 429):
                    blocked.add(host)
            except Exception as e:  # network error
                body = b""
                rec["status"] = "ERROR " + repr(e)[:200]
            low = body[:4000].lower()
            if b"captcha" in low or b"challenge" in low and b"cloudflare" in low:
                rec["challenge_suspected"] = True
                blocked.add(host)
            rec["bytes"] = len(body)
            rec["sha256"] = hashlib.sha256(body).hexdigest()
            with open(os.path.join(out, name), "wb") as fh:
                fh.write(body)
            time.sleep(3)
        with open(os.path.join(out, name + ".receipt.json"), "w") as fh:
            json.dump(rec, fh, indent=1)
        print(json.dumps(rec), flush=True)


if __name__ == "__main__":
    main()
