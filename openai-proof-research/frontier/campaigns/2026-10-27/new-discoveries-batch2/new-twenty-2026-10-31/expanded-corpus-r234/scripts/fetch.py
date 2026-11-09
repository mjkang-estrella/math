import urllib.request,urllib.error,urllib.parse,hashlib,json,datetime,pathlib,sys
D=pathlib.Path(__file__).resolve().parents[1]; denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org','mathdb.com'}
for p in (D/'sources').glob('*.receipt.json'):
 r=json.loads(p.read_text())
 if r.get('status') in (403,429):denied.add(urllib.parse.urlparse(r['url']).hostname)
class Guard(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied:raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Guard())
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 path=D/'sources'/f'{name}.receipt.json'
 if path.exists():raise RuntimeError('never overwrite receipt '+name)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if urllib.parse.urlparse(url).hostname in denied:raise RuntimeError('inherited or session denied host; not requested')
  with op.open(urllib.request.Request(url,headers={'User-Agent':'Research/1.0'}),timeout=20) as r:
   b=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/'sources'/f'{name}.body').write_bytes(b)
 except Exception as e:
  rec.update(error=str(e),status=getattr(e,'code',None))
  if rec['status'] in (403,429):denied.add(urllib.parse.urlparse(url).hostname)
 path.write_text(json.dumps(rec,indent=2)+'\n');print(name,rec)
