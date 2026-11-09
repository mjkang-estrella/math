import urllib.request, urllib.error, urllib.parse, pathlib, sys, datetime, hashlib, json
BASE=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/submodsep-retention-r1')
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,*args): return None
url,name=sys.argv[1:]
d=BASE/'downloads'/name; d.mkdir(exist_ok=False)
op=urllib.request.build_opener(NoRedirect)
r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'hops':[]}
blocked={'api.crossref.org','api.semanticscholar.org','www.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','sciencedirect.com','link.springer.com','www.worldscientific.com'}
for p in (BASE/'downloads').glob('*/receipt.json'):
 old=json.loads(p.read_text())
 for h in old.get('hops',[]):
  if h.get('status') in (403,429): blocked.add(urllib.parse.urlsplit(h['url']).hostname)
for _ in range(5):
 host=urllib.parse.urlsplit(url).hostname
 if host in blocked or ('epubs.siam.org'==host and '/pdf/' in url):
  r['error']='blocked URL'; break
 try:
  resp=op.open(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0 (academic source verification)'}),timeout=35)
 except urllib.error.HTTPError as e: resp=e
 except Exception as e: r['error']=repr(e); break
 h={'url':url,'status':resp.status,'headers':dict(resp.headers)}; r['hops'].append(h)
 if resp.status in (301,302,303,307,308):
  url=urllib.parse.urljoin(url,resp.headers['Location']); continue
 body=resp.read(40000000); (d/'body').write_bytes(body)
 r.update(status=resp.status,final_url=url,sha256=hashlib.sha256(body).hexdigest(),bytes=len(body));break
(d/'receipt.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
