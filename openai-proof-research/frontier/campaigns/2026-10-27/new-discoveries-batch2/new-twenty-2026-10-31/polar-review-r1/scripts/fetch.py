#!/usr/bin/env python3
"""Receipt-keeping fetcher for polar-review-r1.

usage: fetch.py PLAN.json OUTDIR
PLAN.json: {"spacing_s": float, "items": [{"name": "...", "url": "https://..."}]}
OUTDIR must NOT exist; it is created fresh and empty.  Bodies and receipts are written with
open(...,'x') (never overwritten).  TLS verification is always on (default context).  No retries.
Redirects are not followed automatically: a redirect is recorded and followed only if it stays
on the same host and that host has not denied us.  A 403/429 (or a challenge page) marks the
host denied for the rest of the run.  Denied-by-policy hosts are refused up front.
"""
import hashlib, json, os, ssl, sys, time, urllib.error, urllib.parse, urllib.request

POLICY_DENIED = {'api.crossref.org', 'www.crossref.org', 'api.semanticscholar.org', 'www.semanticscholar.org',
                 'export.arxiv.org', 'www.sciencedirect.com', 'sciencedirect.com', 'dblp.org', 'dblp.uni-trier.de'}
UA = 'polar-review-r1-research-fetcher/1.0 (bounded academic prior-art screen)'

class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, *a, **k):
        return None

def main(plan_path, outdir):
    plan = json.load(open(plan_path))
    os.makedirs(outdir)  # fails if it exists: fresh, empty directory
    ctx = ssl.create_default_context()
    opener = urllib.request.build_opener(NoRedirect, urllib.request.HTTPSHandler(context=ctx))
    denied = set()
    for n, item in enumerate(plan['items']):
        if n: time.sleep(plan.get('spacing_s', 2.0))
        url = item['url']; name = item['name']; hops = []
        rec = {'name': name, 'url': url, 'utc': time.strftime('%Y-%m-%dT%H:%M:%SZ', time.gmtime())}
        for hop in range(4):
            host = urllib.parse.urlparse(url).hostname
            if host in POLICY_DENIED or host in denied:
                rec['refused'] = f'host {host} denied (policy or earlier 403/429)'; break
            req = urllib.request.Request(url, headers={'User-Agent': UA, 'Accept': item.get('accept', '*/*')})
            try:
                with opener.open(req, timeout=25) as r:
                    body = r.read(20_000_000)
                    rec.update(status=r.status, final_url=url, headers={k: v for k, v in r.headers.items()
                               if k.lower() in ('content-type', 'content-length', 'last-modified', 'etag', 'date',
                                                'x-ratelimit-remaining', 'x-ratelimit-limit')})
                    low = body[:4000].lower()
                    if b'captcha' in low or b'challenge-platform' in low or b'just a moment' in low:
                        rec['challenge_detected'] = True; denied.add(host)
                    with open(os.path.join(outdir, name), 'xb') as f:
                        f.write(body)
                    rec['sha256'] = hashlib.sha256(body).hexdigest(); rec['bytes'] = len(body)
                    break
            except urllib.error.HTTPError as e:
                rec['status'] = e.code
                if e.code in (301, 302, 303, 307, 308):
                    loc = urllib.parse.urljoin(url, e.headers.get('Location', ''))
                    hops.append({'from': url, 'to': loc, 'status': e.code})
                    if urllib.parse.urlparse(loc).hostname != host:
                        rec['redirect_not_followed'] = loc; break
                    url = loc; continue
                if e.code in (403, 429):
                    denied.add(host); rec['denied'] = True
                rec['error'] = str(e); break
            except Exception as e:  # TLS or network errors: record, no retry, no TLS bypass
                rec['error'] = repr(e); break
        rec['redirects'] = hops
        with open(os.path.join(outdir, name + '.receipt.json'), 'x') as f:
            json.dump(rec, f, indent=1)
        print(json.dumps({k: rec.get(k) for k in ('name', 'status', 'bytes', 'sha256', 'error', 'refused',
                                                    'redirect_not_followed', 'challenge_detected')}))

if __name__ == '__main__':
    main(sys.argv[1], sys.argv[2])
