import urllib.request, urllib.error, json, hashlib, datetime, pathlib, time
L=pathlib.Path(__file__).resolve().parents[1]
denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org'}
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied: raise RuntimeError('redirect to denied host: '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Redirect)
urls=[('arxiv-current','https://arxiv.org/abs/2508.17854'),('openalex-source','https://api.openalex.org/works?search=Structural%20Characterisations%20Trees&per-page=10'),('openalex-authors','https://api.openalex.org/works?search=Kottari%20Sahni&per-page=25'),('pool-head','https://api.github.com/repos/Vilin97/lean-pool/commits/HEAD'),('pool-projects','https://raw.githubusercontent.com/Vilin97/lean-pool/HEAD/LeanPool/projects.yml'),('pool-candidates','https://api.github.com/repos/Vilin97/lean-pool/contents/candidates'),('github-search-1','https://api.github.com/search/repositories?q=%222508.17854%22'),('github-search-2','https://api.github.com/search/repositories?q=%22Kottari%22+%22tree%22')]
for name,url in urls:
 d=L/'downloads'/name; d.mkdir(exist_ok=False)
 receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if urllib.parse.urlparse(url).hostname in denied: raise RuntimeError('host denied already')
  req=urllib.request.Request(url,headers={'User-Agent':'Mathematical-review/1.0','Accept':'*/*'})
  try: r=op.open(req,timeout=12)
  except urllib.error.HTTPError as e:r=e
  body=r.read(); receipt.update(status=r.code,final_url=r.url,headers=dict(r.headers),sha256=hashlib.sha256(body).hexdigest(),bytes=len(body))
  (d/'body').write_bytes(body)
  if r.code in (403,429) or b'captcha' in body[:2000].lower(): denied.add(urllib.parse.urlparse(r.url).hostname)
 except Exception as e: receipt['error']=str(e)
 (d/'receipt.json').write_text(json.dumps(receipt,indent=2))
 print(name,receipt.get('status'),receipt.get('error'),flush=True)
 time.sleep(2)
