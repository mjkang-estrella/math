"""Single bounded HTTP GET; one attempt, no retries, no proxy, TLS verified.
usage: fetch.py URL OUTDIR NAME LOG
OUTDIR must not exist (a fresh empty directory is created per fetch)."""
import sys, os, json, hashlib, datetime, urllib.request, urllib.error, ssl
url, outdir, name, log = sys.argv[1:5]
os.makedirs(outdir, exist_ok=False)
utc = datetime.datetime.now(datetime.timezone.utc).isoformat()
req = urllib.request.Request(url, headers={'User-Agent': 'Mozilla/5.0 (research; bounded single fetch)'})
opener = urllib.request.build_opener(urllib.request.ProxyHandler({}), urllib.request.HTTPSHandler(context=ssl.create_default_context()))
rec = {'utc': utc, 'url': url}
try:
    with opener.open(req, timeout=60) as r:
        body = r.read(30_000_000)
        rec.update(status=r.status, final_url=r.geturl(), content_type=r.headers.get('Content-Type'),
                   last_modified=r.headers.get('Last-Modified'))
except urllib.error.HTTPError as e:
    body = e.read(2_000_000)
    rec.update(status=e.code, final_url=e.geturl(), error='HTTPError')
except Exception as e:
    body = b''
    rec.update(status=None, error=repr(e))
path = os.path.join(outdir, name)
with open(path, 'wb') as f:
    f.write(body)
rec.update(file=path, bytes=len(body), sha256=hashlib.sha256(body).hexdigest())
with open(log, 'a') as f:
    f.write(json.dumps(rec) + '\n')
print(json.dumps(rec))
