import pathlib, urllib.request, urllib.error, urllib.parse, json, hashlib, datetime, sys
D=pathlib.Path(__file__).resolve().parents[1]
denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','sciencedirect.com','dblp.org'}
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text())
 if r.get('status') in (403,429) or r.get('challenge'): denied.add(urllib.parse.urlsplit(r['url']).hostname)
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlsplit(newurl).hostname in denied: raise RuntimeError('redirect to denied host '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
opener=urllib.request.build_opener(Redirect())
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 p=D/'sources'/name
 if pathlib.Path(str(p)+'.receipt.json').exists(): raise RuntimeError('immutable receipt exists '+name)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if urllib.parse.urlsplit(url).hostname in denied: raise RuntimeError('host denied; not requested')
  with opener.open(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0'}),timeout=18) as r:
   b=r.read(30000000); rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),headers=dict(r.headers))
   pathlib.Path(str(p)+'.body').write_bytes(b)
   if b'Just a moment...' in b[:20000] or b'Checking your browser' in b[:20000]: rec['challenge']=True;denied.add(urllib.parse.urlsplit(r.url).hostname)
 except Exception as e:
  rec.update(error=str(e),status=getattr(e,'code',None))
  if rec['status'] in (403,429): denied.add(urllib.parse.urlsplit(url).hostname)
 pathlib.Path(str(p)+'.receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(name,rec.get('status'),rec.get('bytes'),rec.get('error',''))
