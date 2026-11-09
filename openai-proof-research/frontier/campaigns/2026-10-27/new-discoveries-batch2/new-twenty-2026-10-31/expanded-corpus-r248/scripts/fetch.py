"""Fetch URLs into sources/NAME.body with immutable receipts (adapted from r245/scripts/fetch.py).
usage: fetch.py NAME1 URL1 [NAME2 URL2 ...]
Refuses to overwrite a receipt; never retries 403/429/challenge hosts; refuses redirects to denied hosts;
TLS verification stays on (urllib default)."""
import pathlib, urllib.request, urllib.error, urllib.parse, json, hashlib, datetime, sys
D = pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r248')
S = D / 'sources'
S.mkdir(exist_ok=True)
denied = {'api.crossref.org', 'crossref.org', 'www.crossref.org', 'api.semanticscholar.org', 'www.semanticscholar.org',
          'semanticscholar.org', 'export.arxiv.org', 'www.sciencedirect.com', 'sciencedirect.com', 'dblp.org',
          'dblp.uni-trier.de', 'digitalcommons.georgiasouthern.edu', 'web.archive.org', 'archive.org', 'core.ac.uk',
          'www.base-search.net', 'base-search.net'}
for p in S.glob('*.receipt.json'):
    r = json.loads(p.read_text())
    if r.get('status') in (403, 429) or r.get('challenge'):
        denied.add(urllib.parse.urlsplit(r['url']).hostname)
        if r.get('final_url'):
            denied.add(urllib.parse.urlsplit(r['final_url']).hostname)


class Redirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if urllib.parse.urlsplit(newurl).hostname in denied:
            raise RuntimeError('redirect to denied host ' + newurl)
        return super().redirect_request(req, fp, code, msg, headers, newurl)


opener = urllib.request.build_opener(Redirect())
for name, url in zip(sys.argv[1::2], sys.argv[2::2]):
    p = S / name
    if pathlib.Path(str(p) + '.receipt.json').exists():
        print('SKIP immutable receipt exists', name)
        continue
    rec = {'url': url, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    try:
        if urllib.parse.urlsplit(url).hostname in denied:
            raise RuntimeError('host denied; not requested')
        with opener.open(urllib.request.Request(url, headers={'User-Agent': 'MathematicalResearch/1.0'}), timeout=25) as r:
            b = r.read(40000000)
            rec.update(status=r.status, final_url=r.url, sha256=hashlib.sha256(b).hexdigest(), bytes=len(b),
                       content_type=r.headers.get('content-type'))
            pathlib.Path(str(p) + '.body').write_bytes(b)
            if b'Just a moment...' in b[:20000] or b'Checking your browser' in b[:20000] or b'captcha' in b[:5000].lower():
                rec['challenge'] = True
                denied.add(urllib.parse.urlsplit(r.url).hostname)
    except Exception as e:
        rec.update(error=str(e)[:500], status=getattr(e, 'code', None))
        if rec['status'] in (403, 429):
            denied.add(urllib.parse.urlsplit(url).hostname)
    pathlib.Path(str(p) + '.receipt.json').write_text(json.dumps(rec, indent=2) + '\n')
    print(name, rec.get('status'), rec.get('bytes'), rec.get('error', ''))
