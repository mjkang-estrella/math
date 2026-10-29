import os,resource,signal,json,hashlib,urllib.request
from pathlib import Path
from datetime import datetime,timezone
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(65)
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
b=Path(__file__).resolve().parent;log=[]
for name,url in [('dusart.pdf','https://arxiv.org/pdf/1002.0442'),('defant-companion.pdf','https://real.mtak.hu/71424/1/1448.pdf')]:
 t=datetime.now(timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(url,timeout=20) as r:d=r.read(12000000);status=r.status
  (b/'sources'/name).write_bytes(d);log.append(dict(utc=t,url=url,status=status,sha256=hashlib.sha256(d).hexdigest(),file='sources/'+name))
 except Exception as e:log.append(dict(utc=t,url=url,error=str(e)))
(b/'retrieval3.json').write_text(json.dumps(log,indent=2));print(json.dumps(log,indent=2))
