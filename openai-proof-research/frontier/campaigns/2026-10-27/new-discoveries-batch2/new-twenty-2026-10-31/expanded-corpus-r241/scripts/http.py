from pathlib import Path
import urllib.request, urllib.error, urllib.parse, json, hashlib, datetime, sys
D=Path(__file__).resolve().parents[1]; denied={'api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','dblp.org'}
class Guard(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if urllib.parse.urlsplit(newurl).hostname in denied: raise RuntimeError('denied redirect '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(Guard())
def fetch(key,url):
 p=D/'sources'/key; rpath=p.with_name(p.name+'.receipt.json'); assert not p.exists() and not rpath.exists()
 host=urllib.parse.urlsplit(url).hostname
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  if host in denied:raise RuntimeError('host denied; skipped')
  with op.open(urllib.request.Request(url,headers={'User-Agent':'Mathematical research source verification'}),timeout=18) as r:
   body=r.read(); rec.update(status=r.status,final_url=r.url,headers=dict(r.headers))
  p.write_bytes(body);rec.update(sha256=hashlib.sha256(body).hexdigest(),bytes=len(body))
  if b'captcha' in body[:100000].lower() or b'Just a moment' in body[:10000]:denied.add(host);rec['challenge']=True
 except Exception as e:
  rec['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   rec['status']=e.code
   if e.code in (403,429):denied.add(host)
 rpath.write_text(json.dumps(rec,indent=2)+'\n');print(key,rec.get('status'),rec.get('error',''),rec.get('bytes'),flush=True)
if __name__=='__main__':
 todo=json.loads(Path(sys.argv[1]).read_text())
 for key,url in todo:fetch(key,url)
