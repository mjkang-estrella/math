import urllib.request,urllib.error,json,hashlib,datetime,resource,os
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(60,60));resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
p=Path(__file__).resolve().parent/'sources';p.mkdir(exist_ok=True)
def fetch(name,url):
 rec={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  try:r=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathReview/1.0'}),timeout=25)
  except urllib.error.HTTPError as e:r=e
  data=r.read();(p/(name+'.body')).write_bytes(data);rec.update(status=r.code,final_url=r.url,bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 except Exception as e:rec['error']=str(e)
 (p/(name+'.receipt.json')).write_text(json.dumps(rec,indent=2));print(json.dumps(rec),flush=True)
 return json.loads(data) if rec.get('status')==200 and 'api.github.com' in url else None

fetch('bezrukov-record','https://www.mathnet.ru/eng/ppi768')
