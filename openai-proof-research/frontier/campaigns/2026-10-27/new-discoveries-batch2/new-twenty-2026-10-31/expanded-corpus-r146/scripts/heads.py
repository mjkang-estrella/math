# Live registry HEADs via GitHub /commits/HEAD (never /commits/main). TLS verification default.
import json, urllib.request, hashlib, datetime, pathlib
D = pathlib.Path(__file__).resolve().parents[1]
out = {}
for repo in ['openai/math', 'the-omega-institute/trureturing']:
    u = f'https://api.github.com/repos/{repo}/commits/HEAD'
    try:
        req = urllib.request.Request(u, headers={'User-Agent': 'research-lane-fetch/1.0', 'Accept': 'application/vnd.github+json'})
        with urllib.request.urlopen(req, timeout=25) as r: b = r.read(); st = r.status
        j = json.loads(b)
        out[repo] = dict(url=u, status=st, sha=j['sha'], date=j['commit']['committer']['date'], message=j['commit']['message'][:200], body_sha256=hashlib.sha256(b).hexdigest(), tree=j['commit']['tree']['sha'])
    except Exception as e:
        out[repo] = dict(url=u, error=repr(e)[:300])
    out[repo]['utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
(D / 'outputs/registry-heads.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=1))
