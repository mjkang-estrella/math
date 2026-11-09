import urllib.request,urllib.error,hashlib,json,datetime,resource,time
from pathlib import Path
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=Path(__file__).resolve().parent
jobs=[("arxiv-current.html","https://arxiv.org/abs/1407.2823"),("arxiv-source.tar","https://arxiv.org/src/1407.2823v1"),("author-research.html","https://sites.math.rutgers.edu/~nhf12/research.html"),("author-current.html","https://www.canisius.edu/academics/our-schools/school-arts-social-sciences/faculty-and-staff/nathan-fox"),("journal-2015.html","https://cs.uwaterloo.ca/journals/JIS/VOL18/Larsson/larsson8.html"),("classification-2024.html","https://www.sciencedirect.com/science/article/pii/S030439752400392X")]
for name,url in jobs:
 r={"url":url,"utc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"attempts":1}
 try:
  with urllib.request.urlopen(url,timeout=12) as v:
   data=v.read(15000000);r.update(status=v.status,final_url=v.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));p.joinpath(name).write_bytes(data)
 except urllib.error.HTTPError as e:
  data=e.read(1000000);p.joinpath(name+".error").write_bytes(data);r.update(status=e.code,sha256=hashlib.sha256(data).hexdigest(),error=str(e))
 except Exception as e:r.update(status="failed",error=str(e))
 p.joinpath(name+".receipt.json").write_text(json.dumps(r,indent=2));print(json.dumps(r),flush=True)
