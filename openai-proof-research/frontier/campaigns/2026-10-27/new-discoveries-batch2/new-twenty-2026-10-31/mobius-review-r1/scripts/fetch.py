from pathlib import Path
import urllib.request, urllib.parse, urllib.error, json, hashlib,sys,datetime
D=Path(__file__).resolve().parents[1]; denied=D/'denied-hosts.json'
blocked=set(json.loads(denied.read_text())) if denied.exists() else {'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org','dblp1.uni-trier.de','www.researchgate.net','mathdb.com'}
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlparse(newurl).hostname in blocked: raise RuntimeError('Redirect to denied host')
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Redirect)
for label,url in [x.split('|',1) for x in sys.argv[1:]]:
 out=D/'downloads'/label;out.mkdir();r={'url':url,'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  assert urllib.parse.urlparse(url).hostname not in blocked
  with op.open(urllib.request.Request(url,headers={'User-Agent':'Independent-mathematical-review/1.0'}),timeout=28) as f:
   r.update(status=f.status,final_url=f.url,headers=dict(f.headers));b=f.read(40000000)
   if b'captcha' in b[:10000].lower() or b'just a moment' in b[:10000].lower():
    blocked.add(urllib.parse.urlparse(f.url).hostname);r['challenge']=True
   (out/'body').write_bytes(b);r['sha256']=hashlib.sha256(b).hexdigest()
 except Exception as e:
  r['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   r.update(status=e.code,headers=dict(e.headers));(out/'error-body').write_bytes(e.read())
   if e.code in [403,429]:blocked.add(urllib.parse.urlparse(e.url).hostname)
 (out/'receipt.json').write_text(json.dumps(r,indent=2));denied.write_text(json.dumps(sorted(blocked)))
 print(label,r.get('status'),r.get('error',''),flush=True)
