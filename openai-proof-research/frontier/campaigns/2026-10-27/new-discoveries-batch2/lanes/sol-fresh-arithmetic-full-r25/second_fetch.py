import os,resource,signal,urllib.request,json,hashlib
from pathlib import Path
from datetime import datetime,timezone
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(30,30));signal.alarm(60)
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
b=Path(__file__).resolve().parent
items=[('sparse-journal.pdf','https://math.colgate.edu/~integers/p18/p18.pdf'),('masser-shiu.pdf','https://msp.org/pjm/1986/121-2/pjm-v121-n2-p11-s.pdf')]
log=[]
for n,u in items:
 t=datetime.now(timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(u,timeout=18) as r:d=r.read(12000000);s=r.status
  (b/'sources'/n).write_bytes(d);log.append(dict(url=u,utc=t,status=s,sha256=hashlib.sha256(d).hexdigest(),file='sources/'+n))
 except Exception as e:log.append(dict(url=u,utc=t,error=str(e)))
(b/'retrieval2.json').write_text(json.dumps(log,indent=2));print(json.dumps(log,indent=2))
