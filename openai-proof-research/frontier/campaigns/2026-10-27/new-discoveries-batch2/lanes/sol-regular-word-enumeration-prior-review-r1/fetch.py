import urllib.request,urllib.error,sys,json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
class Routes(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if any(s in newurl.lower() for s in ['sciencedirect.com','github.com','githubusercontent.com','codeload.github','google.com']):raise RuntimeError('redirect to parked route '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
url,label=sys.argv[1:]
row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.build_opener(Routes()).open(urllib.request.Request(url,headers={'User-Agent':'Mathematical source review (bounded academic retrieval)'}),timeout=25) as r:
  b=r.read(10000001)
  if len(b)>10000000:raise RuntimeError('body cap')
  row.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
  for folder in ['retrieved','frozen-new']:
   p=L/folder/label;p.parent.mkdir(exist_ok=True);p.write_bytes(b)
  assert (L/'retrieved'/label).read_bytes()==(L/'frozen-new'/label).read_bytes()
  row['challenge']=any(s in b[:100000].lower() for s in [b'captcha',b'just a moment...',b'verify you are human'])
except Exception as e:row['error']=str(e)
with (L/'access.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
print(json.dumps(row))
