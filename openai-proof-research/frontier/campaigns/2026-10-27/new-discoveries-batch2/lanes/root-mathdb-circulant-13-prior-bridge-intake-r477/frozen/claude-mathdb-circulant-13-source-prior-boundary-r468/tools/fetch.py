"""Single-shot public HTTP GET. No retries, default TLS verification, no cookies.

usage: fetch.py NAME URL OUTDIR
Writes OUTDIR/NAME.body and OUTDIR/NAME.meta.json (url, effective url, UTC,
status, selected headers, sha256, size, challenge flag, error). Bytes are
hashed and saved before anyone reads them. Exit 0 on HTTP 200 without a
challenge marker, else 2 (the caller must stop that route, not retry).
"""
import datetime, hashlib, json, os, sys, urllib.error, urllib.request

name, url, outdir = sys.argv[1:4]
os.makedirs(outdir, exist_ok=True)
meta = {'name': name, 'requested_url': url,
        'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
body = b''
req = urllib.request.Request(url, headers={
    'User-Agent': 'bounded-literature-review-script/1.0 (single request, no retries)',
    'Accept': '*/*'})
try:
    with urllib.request.urlopen(req, timeout=60) as r:
        body = r.read(20 * 1024 * 1024)
        meta['status'] = r.status
        meta['effective_url'] = r.geturl()
        meta['headers'] = {k: v for k, v in r.headers.items()
                           if k.lower() in ('content-type', 'content-length', 'last-modified',
                                            'date', 'server', 'x-ratelimit-remaining', 'retry-after')}
except urllib.error.HTTPError as e:
    body = e.read() or b''
    meta['status'] = e.code
    meta['effective_url'] = e.geturl()
    meta['error'] = 'HTTPError %s' % e.code
except Exception as e:  # TLS, DNS, timeout: record and stop
    meta['status'] = None
    meta['error'] = '%s: %s' % (type(e).__name__, e)
low = body[:200000].lower()
markers = [m for m in (b'captcha', b'incapsula', b'cf-chl', b'challenge-platform', b'distil',
                       b'access denied', b'are you a robot', b'just a moment')
           if m in low]
meta['challenge_markers'] = [m.decode() for m in markers]
meta['size'] = len(body)
meta['sha256'] = hashlib.sha256(body).hexdigest()
ok = meta.get('status') == 200 and not markers
meta['usable'] = ok
with open(os.path.join(outdir, name + '.body'), 'wb') as f:
    f.write(body)
with open(os.path.join(outdir, name + '.meta.json'), 'w') as f:
    json.dump(meta, f, indent=1, sort_keys=True)
print(json.dumps({k: meta.get(k) for k in ('name', 'status', 'size', 'sha256', 'usable',
                                           'challenge_markers', 'error')}))
sys.exit(0 if ok else 2)
