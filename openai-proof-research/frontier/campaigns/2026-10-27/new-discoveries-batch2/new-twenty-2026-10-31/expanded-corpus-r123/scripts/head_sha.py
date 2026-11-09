# GET /repos/openai/math/commits/HEAD with Accept: application/vnd.github.sha (returns the bare SHA). One attempt.
import urllib.request, datetime, json, pathlib, hashlib
D = pathlib.Path(__file__).resolve().parents[1]
url = 'https://api.github.com/repos/openai/math/commits/HEAD'; now = datetime.datetime.now(datetime.timezone.utc).isoformat()
try:
    with urllib.request.urlopen(urllib.request.Request(url, headers={'Accept': 'application/vnd.github.sha', 'User-Agent': 'Mathematical research source verification'}), timeout=30) as r:
        b = r.read(); rec = dict(url=url, accept='application/vnd.github.sha', status=r.status, utc=now, body=b.decode().strip(), sha256=hashlib.sha256(b).hexdigest())
except Exception as e:
    rec = dict(url=url, utc=now, error=str(e))
(D / 'sources2' / 'openai-head-sha.receipt.json').write_text(json.dumps(rec, indent=2) + '\n'); print(rec)
