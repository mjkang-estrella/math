from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime,sys
L=Path(__file__).resolve().parent; D=L/'http';D.mkdir(exist_ok=True)
denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org','link.springer.com'}
from urllib.parse import urlparse
class Guard(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urlparse(newurl).hostname in denied: raise RuntimeError('redirect denied '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Guard)
def fetch(name,url):
 p=D/name
 if p.exists() or (D/(name+'.receipt.json')).exists(): return
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 if urlparse(url).hostname in denied: rec['blocked']='inherited denial';return
 try:
  with op.open(urllib.request.Request(url,headers={'User-Agent':'Research source review (public mathematical manuscripts)'}),timeout=25) as r:
   b=r.read();p.write_bytes(b);rec.update(status=r.status,final_url=r.url,headers=dict(r.headers),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
   if b'captcha' in b[:5000].lower() or b'cf-chl-' in b[:5000].lower(): denied.add(urlparse(r.url).hostname);rec['challenge']=True
 except Exception as e:
  rec['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   rec['status']=e.code;rec['headers']=dict(e.headers);p.write_bytes(e.read())
   if e.code in (403,429):denied.add(urlparse(url).hostname)
 (D/(name+'.receipt.json')).write_text(json.dumps(rec,indent=2));print(name,rec.get('status',rec.get('error')))
if __name__=='__main__':
 jobs=json.loads((L/sys.argv[1]).read_text())
 for name,url in jobs:fetch(name,url)
