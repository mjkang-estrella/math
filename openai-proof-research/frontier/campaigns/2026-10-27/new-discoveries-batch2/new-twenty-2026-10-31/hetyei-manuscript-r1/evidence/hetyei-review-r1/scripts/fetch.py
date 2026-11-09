#!/usr/bin/env python3
"""Fetch ONE URL into a new file with a receipt. TLS verification left at default (on).
Usage: fetch.py URL OUTFILE [ACCEPT]
- refuses to overwrite OUTFILE or OUTFILE.receipt.json
- follows redirects only within the same host (others are recorded, not followed)
- never retries; records HTTP status / error in the receipt."""
import hashlib, json, os, sys, time, urllib.request, urllib.error, urllib.parse

DENY = ('api.crossref.org', 'crossref.org', 'api.semanticscholar.org', 'semanticscholar.org',
        'export.arxiv.org', 'sciencedirect.com', 'www.sciencedirect.com', 'dblp.org', 'dblp.uni-trier.de')

url, out = sys.argv[1], sys.argv[2]
accept = sys.argv[3] if len(sys.argv) > 3 else '*/*'
rec_path = out + '.receipt.json'
if os.path.exists(out) or os.path.exists(rec_path):
    sys.exit('refusing to overwrite')
parent = os.path.dirname(os.path.abspath(out))
if os.path.exists(parent) and os.listdir(parent):
    sys.exit('download directory must be fresh and empty: ' + parent)
os.makedirs(parent, exist_ok=True)
host0 = urllib.parse.urlsplit(url).hostname
if any(host0 == d or host0.endswith('.' + d) for d in DENY):
    sys.exit('denied host ' + host0)

class SameHost(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        h = urllib.parse.urlsplit(newurl).hostname
        if h != host0:
            raise urllib.error.HTTPError(newurl, code, 'cross-host redirect not followed: ' + newurl, headers, fp)
        return super().redirect_request(req, fp, code, msg, headers, newurl)

opener = urllib.request.build_opener(SameHost)
req = urllib.request.Request(url, headers={'User-Agent': 'math-research-review/1.0 (python-urllib)', 'Accept': accept})
receipt = {'url': url, 'time_utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime()), 'out': out}
try:
    with opener.open(req, timeout=60) as r:
        data = r.read(40 * 1024 * 1024 + 1)
        receipt.update(status=r.status, final_url=r.geturl(), content_type=r.headers.get('Content-Type'),
                       length=len(data), sha256=hashlib.sha256(data).hexdigest())
        if len(data) > 40 * 1024 * 1024:
            receipt['error'] = 'too large, not saved'
        else:
            with open(out, 'xb') as f:
                f.write(data)
except urllib.error.HTTPError as e:
    receipt.update(status=e.code, error=str(e.reason)[:300])
except Exception as e:
    receipt.update(status=None, error=repr(e)[:300])
with open(rec_path, 'x') as f:
    json.dump(receipt, f, indent=1)
print(json.dumps(receipt))
