import urllib.request,urllib.error,urllib.parse,sys,json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
class SafeRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if any(s in newurl.lower() for s in ['sciencedirect','github','google.com','semanticscholar','codeload']):raise ValueError('parked redirect '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 r=dict(name=name,url=url,time=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  if any(s in url.lower() for s in ['sciencedirect','github','google.com','semanticscholar','codeload']):raise ValueError('parked route')
  with urllib.request.build_opener(SafeRedirect).open(urllib.request.Request(url,headers={'User-Agent':'Bounded academic source review; Python urllib'}),timeout=25) as f:
   b=f.read(8000001);assert len(b)<=8000000
   r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
  p=L/'current'/name;p.parent.mkdir(exist_ok=True);p.write_bytes(b)
  r.update(path=str(p.relative_to(L)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),frozen_before_read=True)
 except Exception as e:
  r['error']=str(e)
  if isinstance(e,urllib.error.HTTPError):
   b=e.read(200000);p=L/'current'/(name+'.error');p.parent.mkdir(exist_ok=True);p.write_bytes(b);r.update(status=e.code,path=str(p.relative_to(L)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
 with (L/'access.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r))
