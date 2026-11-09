import sys, pathlib, urllib.request, urllib.parse, json, hashlib, datetime
ROOT=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/orientdom-priorart-r1')
state=ROOT/'denied-hosts.json'
denied=set(json.loads(state.read_text())) if state.exists() else set()
forbidden={'sciencedirect.com','api.crossref.org','semanticscholar.org','api.semanticscholar.org','link.springer.com','worldscientific.com'}
class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self,*a,**k): return None
opener=urllib.request.build_opener(NoRedirect())
url=sys.argv[1]; label=sys.argv[2]
dest=ROOT/'downloads'/label
dest.mkdir() # must be fresh
rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'redirects':[]}
try:
    for i in range(6):
        host=urllib.parse.urlparse(url).hostname
        if any(host==d or host.endswith('.'+d) for d in denied|forbidden): raise RuntimeError('blocked host '+host)
        if host=='export.arxiv.org' and '/api/' in url: raise RuntimeError('arXiv API prohibited')
        try: response=opener.open(urllib.request.Request(url,headers={'User-Agent':'Public mathematical literature research (no authentication)'}),timeout=35)
        except urllib.error.HTTPError as e:
            if e.code in (301,302,303,307,308):
                target=urllib.parse.urljoin(url,e.headers['Location']); rec['redirects'].append({'from':url,'to':target,'status':e.code}); url=target; continue
            if e.code in (403,429): denied.add(host)
            raise
        data=response.read(40000001)
        if len(data)>40000000: raise RuntimeError('download size cap')
        (dest/'body').write_bytes(data)
        rec.update(status=response.status,final_url=url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),content_type=response.headers.get('Content-Type'))
        if b'Just a moment' in data[:10000] or b'Checking your browser' in data[:10000]:
            denied.add(host); rec['challenge']=True
        break
except Exception as e: rec.update(status=getattr(e,'code','ERROR'),error=str(e),final_url=url)
state.write_text(json.dumps(sorted(denied),indent=2))
(dest/'receipt.json').write_text(json.dumps(rec,indent=2))
print(json.dumps(rec))
