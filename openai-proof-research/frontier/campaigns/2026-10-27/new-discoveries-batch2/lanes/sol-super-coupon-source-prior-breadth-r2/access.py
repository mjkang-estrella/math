from pathlib import Path
import urllib.request,urllib.error,hashlib,json,datetime,sys
L=Path(__file__).resolve().parent
class SafeRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if any(x in newurl.lower() for x in ['github','sciencedirect','google.com','captcha','challenge']):raise RuntimeError('blocked redirect '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
def fetch(name,url):
 records=json.loads((L/'access.json').read_text()) if (L/'access.json').exists() else []
 r=dict(name=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'Mathematical-source-review/1.0'})
  with urllib.request.build_opener(SafeRedirect()).open(req,timeout=35) as f:
   b=f.read(12000000);r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
  if any(x in b[:20000].lower() for x in [b'cf-chl-',b'verify you are human',b'captcha']):raise RuntimeError('challenge; stop route')
  h=hashlib.sha256(b).hexdigest();p=L/'retrieved'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(b)
  q=L/'frozen-live'/name;q.parent.mkdir(exist_ok=True);q.write_bytes(b)
  assert hashlib.sha256(p.read_bytes()).hexdigest()==hashlib.sha256(q.read_bytes()).hexdigest()==h
  r.update(sha256=h,bytes=len(b),original=str(p),copy=str(q))
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 records.append(r);(L/'access.json').write_text(json.dumps(records,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k not in ['headers']}))
if __name__=='__main__':fetch(*sys.argv[1:])
