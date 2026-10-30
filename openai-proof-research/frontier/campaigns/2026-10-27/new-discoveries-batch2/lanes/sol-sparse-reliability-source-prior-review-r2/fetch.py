from pathlib import Path
import sys,json,datetime,hashlib,urllib.request,urllib.error
P=Path(__file__).resolve().parent
class SafeRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,req,fp,code,msg,headers,newurl):
  if any(x in newurl.lower() for x in ['sciencedirect.com','github.com','githubusercontent.com','google.com','colibri.udelar.edu.uy']):
   raise RuntimeError('denied route redirect stopped: '+newurl)
  return super().redirect_request(req,fp,code,msg,headers,newurl)
op=urllib.request.build_opener(SafeRedirect)
name,url=sys.argv[1:]
row={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':'retrieved/'+name}
(P/'retrieved').mkdir(exist_ok=True)
try:
 req=urllib.request.Request(url,headers={'User-Agent':'Research review (bounded public scholarly source retrieval)'})
 with op.open(req,timeout=22) as r:
  data=r.read(6000001)
  if len(data)>6000000:raise RuntimeError('6MB body cap exceeded')
  row.update(status=r.status,final_url=r.url,content_type=r.headers.get('Content-Type'))
except urllib.error.HTTPError as e:
 data=e.read(1000000);row.update(status=e.code,error=str(e),final_url=e.url)
except Exception as e:
 data=b'';row['error']=repr(e)
if data:
 (P/'retrieved'/name).write_bytes(data)
 row.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
with (P/'retrieval.jsonl').open('a') as f:f.write(json.dumps(row)+'\n')
print(json.dumps(row))
