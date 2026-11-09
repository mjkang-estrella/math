import hashlib, json, os, sys, datetime, urllib.request, urllib.error, urllib.parse
# Usage: fetch.py LABEL URL   (single attempt; no retries; stops a host after any 403/429/challenge)
L = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/lanes/claude-richardson-prior-substantive-r2'
LOG = L + '/http.jsonl'
STOPS = L + '/stopped-hosts.json'
INHERITED_DENIED = ['api.github.com', 'raw.githubusercontent.com', 'codeload.github.com', 'github.com',
                    'sciencedirect.com', 'www.sciencedirect.com', 'google.com', 'www.google.com', 'scholar.google.com']
label, url = sys.argv[1], sys.argv[2]
host = urllib.parse.urlparse(url).hostname
stopped = json.load(open(STOPS)) if os.path.exists(STOPS) else {}
now = lambda: datetime.datetime.now(datetime.timezone.utc).isoformat()
rec = {'label': label, 'url': url, 'utc': now()}
if any(host == d or host.endswith('.' + d) for d in INHERITED_DENIED) or host in stopped:
    rec['refused'] = 'inherited or lane-stopped denial route; not attempted'
    open(LOG, 'a').write(json.dumps(rec) + '\n'); print(json.dumps(rec)); sys.exit(2)
os.makedirs(L + '/retrieved', exist_ok=True)
req = urllib.request.Request(url, headers={'User-Agent': 'research-prior-art-check/1.0 (bounded single-request)'})
try:
    r = urllib.request.urlopen(req, timeout=60)
    body, status, final = r.read(), r.status, r.geturl()
except urllib.error.HTTPError as e:
    body, status, final = e.read(), e.code, e.geturl()
except Exception as e:
    rec['error'] = repr(e)
    open(LOG, 'a').write(json.dumps(rec) + '\n'); print(json.dumps(rec)); sys.exit(3)
low = body[:20000].lower()
challenge = status in (403, 429) or (status == 503) or b'captcha' in low or b'cf-challenge' in low or b'are you a robot' in low
rec.update({'status': status, 'final_url': final, 'bytes': len(body), 'sha256': hashlib.sha256(body).hexdigest(), 'challenge_or_denial': challenge})
if challenge:
    stopped[host] = rec['utc']; json.dump(stopped, open(STOPS, 'w'), indent=1)
else:
    p = L + '/retrieved/' + label
    open(p, 'wb').write(body); rec['path'] = 'retrieved/' + label
open(LOG, 'a').write(json.dumps(rec) + '\n')
print(json.dumps({k: rec[k] for k in rec if k != 'url'}))
