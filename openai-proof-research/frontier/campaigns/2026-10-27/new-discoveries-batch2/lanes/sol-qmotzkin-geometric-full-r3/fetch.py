import resource,os,json,hashlib,urllib.request,datetime
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(30,30))
for v in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[v]='1'
p=Path(__file__).parent
urls=[('q-lommel.html','https://arxiv.org/html/1407.0217'),('source.html','https://arxiv.org/html/1805.00113v1')]
r=[]
for name,url in urls:
 now=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(url,timeout=25) as f: data=f.read();status=f.status
  (p/'sources'/name).write_bytes(data)
  r.append(dict(url=url,retrieved_utc=now,status=status,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),file='sources/'+name))
 except Exception as e:r.append(dict(url=url,retrieved_utc=now,error=str(e),retry=False))
 (p/'retrievals.json').write_text(json.dumps(r,indent=2))
print(json.dumps(r,indent=2))
