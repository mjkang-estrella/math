import sys,json,hashlib,datetime,urllib.request,urllib.error
from pathlib import Path
L=Path(__file__).resolve().parent
(L/'access').mkdir(exist_ok=True)
class Redirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if any(s in newurl.lower() for s in ['sciencedirect','github','google.com','captcha']):
   raise RuntimeError('blocked redirect '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 row={'url':url,'access_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'ResearchSourceReview/1.0'})
  with urllib.request.build_opener(Redirect()).open(req,timeout=22) as r:
   row.update(status=r.status,final_url=r.url);data=r.read(12000000)
  p=L/'access'/name;p.write_bytes(data);p.chmod(0o444)
  row.update(file=str(p.relative_to(L)),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),frozen_before_read=True)
 except Exception as e:row.update(error=str(e),status=getattr(e,'code',None))
 (L/'access'/(name+'.receipt.json')).write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row))
