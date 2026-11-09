import pathlib,urllib.request,urllib.error,hashlib,json,datetime,sys
D=pathlib.Path(__file__).resolve().parents[1]; denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org','mathdb.com','api.arxiv.org','palomar'}
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied: raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Redirect)
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 p=D/'sources'/name
 if p.exists() or p.with_suffix(p.suffix+'.receipt.json').exists(): print('EXISTS',name);continue
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if urllib.parse.urlparse(url).hostname in denied: raise RuntimeError('denied host')
  with op.open(urllib.request.Request(url,headers={'User-Agent':'Research-reading/1.0'}),timeout=30) as f:
   b=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));p.write_bytes(b)
  if b'captcha' in b[:10000].lower(): denied.add(urllib.parse.urlparse(url).hostname);r['challenge_suspected']=True
 except urllib.error.HTTPError as e:
  b=e.read();r.update(status=e.code,error=str(e),sha256=hashlib.sha256(b).hexdigest());p.write_bytes(b)
  if e.code in (403,429):denied.add(urllib.parse.urlparse(url).hostname)
 except Exception as e:r['error']=str(e)
 p.with_suffix(p.suffix+'.receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(name,r.get('status'),r.get('error',''),r.get('bytes',''))
