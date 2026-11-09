import sys,json,urllib.request,urllib.error,hashlib,datetime,resource
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(90,90));resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,)*2)
o=Path(__file__).parent
for name,url in json.loads(sys.argv[1]):
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mathematical-literature-review/1.0'}),timeout=25) as f:
   data=f.read(24*1024**2);r.update(status=f.status,final_url=f.url,content_type=f.headers.get('Content-Type'))
 except urllib.error.HTTPError as e:
  data=e.read(1024**2);r.update(status=e.code,final_url=e.url)
 except Exception as e:
  data=b'';r.update(error=str(e))
 (o/(name+'.body')).write_bytes(data);r.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(o/(name+'.receipt.json')).write_text(json.dumps(r,indent=2));print(name,r)
