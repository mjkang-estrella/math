import urllib.request,urllib.error,hashlib,json,datetime,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]
blocked={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','sciencedirect.com','dblp.org','dblp.uni-trier.de','mathdb.com'}
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text())
 if r.get('status') in (403,429) or r.get('challenge'):blocked.add(urllib.parse.urlparse(r['url']).hostname)
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in blocked:raise RuntimeError('redirect to denied host '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 dest=D/'sources'/name
 if pathlib.Path(str(dest)+'.receipt.json').exists():raise RuntimeError('receipt exists '+name)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if urllib.parse.urlparse(url).hostname in blocked:raise RuntimeError('inherited or current denied host')
  with urllib.request.build_opener(Redirect).open(urllib.request.Request(url,headers={'User-Agent':'Research source review'}),timeout=18) as r:
   b=r.read();rec.update(status=r.status,final_url=r.url,headers=dict(r.headers),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));pathlib.Path(str(dest)+'.body').write_bytes(b)
   if b'captcha' in b[:200000].lower() or b'Just a moment...' in b[:200000]:rec['challenge']=True;blocked.add(urllib.parse.urlparse(r.url).hostname)
 except Exception as e:
  rec.update(error=str(e),status=getattr(e,'code',None))
  if rec['status'] in (403,429):blocked.add(urllib.parse.urlparse(url).hostname)
 pathlib.Path(str(dest)+'.receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(name,rec.get('status'),rec.get('error',''),rec.get('bytes',''),flush=True)
