# spaced unauthenticated GitHub repository searches; stop on 403/429; receipts kept, never overwritten
import urllib.request, urllib.parse, json, sys, time, hashlib, datetime, pathlib, ssl
D = pathlib.Path(sys.argv[1]).resolve() / 'sources'
qs = sys.argv[2:]
for i, q in enumerate(qs):
    name = f'ghsearch-{i}'
    rp = D / f'{name}.receipt.json'
    if rp.exists(): print(name, 'exists'); continue
    url = 'https://api.github.com/search/repositories?q=' + urllib.parse.quote(q)
    rec = {'url': url, 'query': q, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        with urllib.request.urlopen(urllib.request.Request(url, headers={'User-Agent': 'math-research-source-review/1.0', 'Accept': 'application/vnd.github+json'}), timeout=30, context=ssl.create_default_context()) as r:
            b = r.read(); rec.update(status=r.status, sha256=hashlib.sha256(b).hexdigest(), bytes=len(b))
            (D / f'{name}.body').write_bytes(b)
            d = json.loads(b); rec['total_count'] = d.get('total_count'); rec['repos'] = [x['full_name'] for x in d.get('items', [])[:10]]
    except Exception as e:
        rec.update(error=str(e)[:200], status=getattr(e, 'code', None))
    rp.write_text(json.dumps(rec, indent=2) + '\n'); print(name, q, rec.get('status'), rec.get('total_count'), rec.get('repos'))
    if rec.get('status') in (403, 429): print('STOP on denial'); break
    time.sleep(8)
