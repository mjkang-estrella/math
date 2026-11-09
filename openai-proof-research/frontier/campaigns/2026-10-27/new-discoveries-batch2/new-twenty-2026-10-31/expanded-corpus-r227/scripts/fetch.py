import pathlib, json, urllib.request, urllib.error, urllib.parse, hashlib, datetime, sys, time
# Usage: fetch.py LANE_DIR PLAN_JSON   (plan: list of [key, url])
# Never overwrites; records a receipt per key; never retries; refuses denied hosts
# and redirects to denied hosts. TLS verification is left at the default (on).
D = pathlib.Path(sys.argv[1]).resolve()
S = D / 'sources'
blocked = {'api.crossref.org', 'api.semanticscholar.org', 'export.arxiv.org', 'www.sciencedirect.com', 'dblp.org', 'mathdb.com'}
for p in S.glob('*.receipt.json'):
    r = json.loads(p.read_text())
    if r.get('status') in [401, 403, 429] or r.get('challenge'):
        blocked.add(urllib.parse.urlsplit(r['url']).hostname)
class Redirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if urllib.parse.urlsplit(newurl).hostname in blocked:
            raise RuntimeError('redirect to denied host ' + newurl)
        return super().redirect_request(req, fp, code, msg, headers, newurl)
opener = urllib.request.build_opener(Redirect)
plan = json.loads(pathlib.Path(sys.argv[2]).read_text())
for key, url in plan:
    p = S / key
    rp = p.with_name(p.name + '.receipt.json')
    if p.exists() or rp.exists():
        print('skip existing', key); continue
    r = {'url': url, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        if urllib.parse.urlsplit(url).hostname in blocked:
            raise RuntimeError('host denied; not attempted')
        try:
            response = opener.open(urllib.request.Request(url, headers={'User-Agent': 'research-source-check/1.0'}), timeout=25)
        except urllib.error.HTTPError as e:
            response = e
        with response as f:
            data = f.read(30_000_000)
            r.update(status=f.status, final_url=f.url, content_type=f.headers.get('Content-Type'))
        p.write_bytes(data)
        r.update(sha256=hashlib.sha256(data).hexdigest(), bytes=len(data))
        if r['status'] in [401, 403, 429]:
            blocked.add(urllib.parse.urlsplit(url).hostname)
        low = data[:4000].lower()
        if b'captcha' in low or b'challenge-platform' in low:
            r['challenge'] = True; blocked.add(urllib.parse.urlsplit(url).hostname)
    except Exception as e:
        r['error'] = repr(e)
    rp.write_text(json.dumps(r, indent=2) + '\n')
    print(key, r.get('status', r.get('error')), r.get('bytes'), flush=True)
    time.sleep(1.0)
