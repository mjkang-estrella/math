import os,resource,signal,time,json,hashlib,urllib.request
from pathlib import Path
from datetime import datetime,timezone
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(30,30));signal.alarm(100)
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
b=Path(__file__).resolve().parent
items=[('farhi.pdf','https://cs.uwaterloo.ca/journals/JIS/VOL15/Farhi/farhi10.pdf'),('iterates.pdf','https://arxiv.org/pdf/1506.05426'),('sparse.pdf','https://arxiv.org/pdf/1412.3080'),('clopen.html','https://clopen.solutions/')]
log=[]
for name,url in items:
 t=datetime.now(timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(url,timeout=18) as r: data=r.read(12000000);status=r.status
  (b/'sources'/name).write_bytes(data);log.append(dict(url=url,utc=t,status=status,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),file='sources/'+name))
 except Exception as e:log.append(dict(url=url,utc=t,error=str(e)))
(b/'retrieval.json').write_text(json.dumps(log,indent=2));print(json.dumps(log,indent=2))
