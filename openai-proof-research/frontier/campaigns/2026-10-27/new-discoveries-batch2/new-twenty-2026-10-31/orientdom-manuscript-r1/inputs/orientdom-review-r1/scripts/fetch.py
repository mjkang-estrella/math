from pathlib import Path
import urllib.request,urllib.error,urllib.parse,json,hashlib,datetime,sys,time
R=Path(sys.argv[1]); denied=set(['api.crossref.org','api.semanticscholar.org','export.arxiv.org','www.sciencedirect.com','sciencedirect.com'])
f=R/'downloads/denied.json'
if f.exists():denied.update(json.loads(f.read_text()))
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,h,newurl):
  if urllib.parse.urlparse(newurl).hostname in denied:raise RuntimeError('redirect to denied host')
  return super().redirect_request(req,fp,code,msg,h,newurl)
op=urllib.request.build_opener(Redirect())
for label,url in zip(sys.argv[2::2],sys.argv[3::2]):
 d=R/'downloads'/label;d.mkdir(exist_ok=False)
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  host=urllib.parse.urlparse(url).hostname
  if host in denied:raise RuntimeError('host already denied')
  with op.open(urllib.request.Request(url,headers={'User-Agent':'Independent-math-review/1.0'}),timeout=20) as res:
   b=res.read(25_000_001);assert len(b)<=25_000_000
   rec.update(status=res.status,final_url=res.url,sha256=hashlib.sha256(b).hexdigest());(d/'body').write_bytes(b)
 except Exception as e:
  rec['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   rec['status']=e.code
   if e.code in (403,429):denied.add(host)
 (d/'receipt.json').write_text(json.dumps(rec,indent=2));print(json.dumps(rec),flush=True)
 f.write_text(json.dumps(sorted(denied)))
 time.sleep(2)
