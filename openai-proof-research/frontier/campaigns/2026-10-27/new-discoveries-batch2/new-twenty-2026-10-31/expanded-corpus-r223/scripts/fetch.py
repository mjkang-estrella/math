import urllib.request, hashlib, json, datetime, pathlib, sys
# usage: fetch.py LANE_DIR name url [name url ...]; never overwrites an existing receipt.
D = pathlib.Path(sys.argv[1]).resolve()
S = D / 'sources'
args = sys.argv[2:]
for name, url in zip(args[0::2], args[1::2]):
    rp = S / f'{name}.receipt.json'
    if rp.exists():
        print(name, 'receipt exists; skipped')
        continue
    rec = {'url': url, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        req = urllib.request.Request(url, headers={'User-Agent': 'Math-research-source-review/1.0'})
        with urllib.request.urlopen(req, timeout=25) as r:
            b = r.read()
            rec.update(status=r.status, final_url=r.url, sha256=hashlib.sha256(b).hexdigest(), bytes=len(b),
                       content_type=r.headers.get('Content-Type'))
            (S / f'{name}.body').write_bytes(b)
    except Exception as e:
        rec.update(error=str(e), status=getattr(e, 'code', None))
    rp.write_text(json.dumps(rec, indent=2) + '\n')
    print(name, {k: rec.get(k) for k in ('status', 'final_url', 'bytes', 'error')})
