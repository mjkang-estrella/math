import urllib.request, urllib.error, urllib.parse, pathlib, json, hashlib, datetime, sys
D=pathlib.Path(__file__).resolve().parents[1]
blocked={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','sciencedirect.com','dblp.org'}
f=D/'outputs/denied-hosts.json'
if f.exists(): blocked.update(json.loads(f.read_text()))
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self, req, fp, code, msg, headers, newurl):
  if urllib.parse.urlparse(newurl).hostname in blocked: raise RuntimeError('redirect to denied host blocked')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Redirect)
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 p=D/'sources'/name
 if p.with_suffix(p.suffix+'.receipt.json').exists(): raise RuntimeError('receipt already exists')
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 host=urllib.parse.urlparse(url).hostname
 try:
  if host in blocked: raise RuntimeError('denied host skipped')
  with op.open(urllib.request.Request(url,headers={'User-Agent':'MathematicalSourceReview/1.0'}),timeout=25) as r:
   b=r.read(); rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
   p.write_bytes(b)
   if b'captcha' in b.lower() or b'bot challenge' in b.lower(): blocked.add(host);rec['challenge_marker']=True
 except Exception as e:
  rec.update(error=str(e),status=getattr(e,'code',None))
  if rec['status'] in (403,429): blocked.add(host)
 p.with_suffix(p.suffix+'.receipt.json').write_text(json.dumps(rec,indent=2)+'\n')
 f.write_text(json.dumps(sorted(blocked))+'\n'); print(name,rec)
