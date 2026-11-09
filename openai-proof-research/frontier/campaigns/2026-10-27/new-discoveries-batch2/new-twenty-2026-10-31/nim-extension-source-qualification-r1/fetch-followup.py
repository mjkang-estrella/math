import urllib.request,urllib.error,hashlib,json,datetime,resource,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent
jobs=[("author-thesis.pdf","https://sites.math.rutgers.edu/~nhf12/Thesis.pdf"),("author-subgames.txt","https://sites.math.rutgers.edu/~nhf12/research/subgames.txt")]
for name,url in jobs:
 r={"url":url,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"attempts":1}
 try:
  with urllib.request.urlopen(url,timeout=12) as v:
   data=v.read(15000000);r.update(status=v.status,final_url=v.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));p.joinpath(name).write_bytes(data)
 except urllib.error.HTTPError as e:
  data=e.read(1000000);p.joinpath(name+".error").write_bytes(data);r.update(status=e.code,sha256=hashlib.sha256(data).hexdigest(),error=str(e))
 except Exception as e:r.update(status="failed",error=str(e))
 p.joinpath(name+".receipt.json").write_text(json.dumps(r,indent=2));print(json.dumps(r),flush=True)
