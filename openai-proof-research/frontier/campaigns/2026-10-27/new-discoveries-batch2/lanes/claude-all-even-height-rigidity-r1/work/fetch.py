"""Bounded public retrieval with receipts.  One attempt per URL; stops on
403/429/challenge-like responses (no retry).  Appends JSON lines to
http.jsonl and writes bodies to sources/<name>.
Usage: fetch.py name url [name url ...]"""
import sys, os, json, hashlib, datetime, urllib.request, urllib.error

lane = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.makedirs(os.path.join(lane, 'sources'), exist_ok=True)
log = os.path.join(lane, 'http.jsonl')
args = sys.argv[1:]
for name, url in zip(args[::2], args[1::2]):
    utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
    rec = {'utc': utc, 'url': url, 'file': 'sources/' + name}
    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'research-lane/1.0 (bounded prior-art screen)'})
        with urllib.request.urlopen(req, timeout=40) as r:
            body = r.read()
            rec.update(status=r.status, final_url=r.geturl())
    except urllib.error.HTTPError as e:
        body = e.read() if hasattr(e, 'read') else b''
        rec.update(status=e.code, final_url=url, error=str(e))
    except Exception as e:
        body = b''
        rec.update(status=None, error=repr(e))
    if body:
        open(os.path.join(lane, 'sources', name), 'wb').write(body)
    rec.update(bytes=len(body), sha256=hashlib.sha256(body).hexdigest())
    low = body[:4000].lower()
    if rec.get('status') in (403, 429) or b'captcha' in low or b'challenge' in low:
        rec['stop'] = 'access-control/challenge: recorded once, not retried'
    open(log, 'a').write(json.dumps(rec) + '\n')
    print(json.dumps(rec))
    if rec.get('stop'):
        break
