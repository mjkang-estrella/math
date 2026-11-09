"""Bounded single-URL fetch. Usage: fetch.py LANE NAME URL
Saves body to LANE/downloads/NAME/body (fresh empty dir), appends a receipt to
LANE/receipts/access.jsonl. Never retries. Classifies 403/429 and challenge
pages as access failures (STOP). Body is not interpreted here."""
import sys, os, json, hashlib, datetime, urllib.request, urllib.error
lane, name, url = sys.argv[1], sys.argv[2], sys.argv[3]
MAX = 40 * 1024 * 1024
d = os.path.join(lane, 'downloads', name)
os.makedirs(d, exist_ok=False)
rec = {'name': name, 'url': url, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0 (X11; Linux x86_64) bounded-research-fetch/1.0', 'Accept': '*/*'})
body = b''
try:
    with urllib.request.urlopen(req, timeout=25) as r:
        body = r.read(MAX + 1)
        rec.update(status=r.status, final_url=r.geturl(), content_type=r.headers.get('Content-Type'))
except urllib.error.HTTPError as e:
    body = e.read(MAX + 1) if hasattr(e, 'read') else b''
    rec.update(status=e.code, final_url=e.geturl(), content_type=e.headers.get('Content-Type') if e.headers else None)
except Exception as e:
    rec['failure'] = repr(e)
rec['truncated'] = len(body) > MAX
body = body[:MAX]
if body:
    p = os.path.join(d, 'body')
    open(p, 'wb').write(body)
    rec.update(file=p, bytes=len(body), sha256=hashlib.sha256(body).hexdigest())
low = body[:200000].lower()
marks = [m for m in (b'incapsula', b'captcha', b'cf-chl', b'just a moment', b'request unsuccessful', b'are you a robot', b'challenge-platform', b'access denied') if m in low]
st = rec.get('status')
rec['access_class'] = ('failure' if 'failure' in rec else
                       'STOP-denied' if st in (401, 403, 429) else
                       'STOP-challenge' if marks else
                       'http-error' if st and st >= 400 else 'ok')
rec['challenge_markers'] = [m.decode() for m in marks]
open(os.path.join(lane, 'receipts', 'access.jsonl'), 'a').write(json.dumps(rec) + '\n')
print(json.dumps(rec))
