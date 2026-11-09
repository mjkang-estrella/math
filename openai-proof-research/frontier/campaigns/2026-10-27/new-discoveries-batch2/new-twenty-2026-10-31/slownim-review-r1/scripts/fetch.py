import urllib.request, urllib.error, urllib.parse, pathlib, json, hashlib, datetime, sys, time
root=pathlib.Path(__file__).resolve().parents[1]
denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','sciencedirect.com'}
for p in (root/'http').glob('*/receipt.json'):
 r=json.loads(p.read_text()); denied.update(r.get('denied_hosts',[]))
class Safe(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied: raise RuntimeError('redirect to denied host blocked: '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
for url in sys.argv[1:]:
 d=root/'http'/datetime.datetime.now(datetime.timezone.utc).strftime('%Y%m%dT%H%M%S%fZ'); d.mkdir()
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if urllib.parse.urlparse(url).hostname in denied: raise RuntimeError('previously denied host blocked')
  req=urllib.request.Request(url,headers={'User-Agent':'Independent-mathematical-review/1.0'})
  with urllib.request.build_opener(Safe()).open(req,timeout=22) as f:
   r.update(status=f.status,final_url=f.url,headers=dict(f.headers)); b=f.read(30000000)
   (d/'body').write_bytes(b); r['sha256']=hashlib.sha256(b).hexdigest()
   if b'cf-chl-' in b or b'Just a moment...' in b:
    denied.add(urllib.parse.urlparse(f.url).hostname); r['challenge']=True
 except Exception as e:
  r['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   r.update(status=e.code,headers=dict(e.headers)); (d/'body').write_bytes(e.read())
   if e.code in (403,429): denied.add(urllib.parse.urlparse(e.url).hostname)
 r['denied_hosts']=sorted(denied)
 (d/'receipt.json').write_text(json.dumps(r,indent=2)); print(d.name,json.dumps(r))
