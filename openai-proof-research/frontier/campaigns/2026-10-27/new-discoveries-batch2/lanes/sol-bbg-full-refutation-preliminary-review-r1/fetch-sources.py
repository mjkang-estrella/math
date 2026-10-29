import os,resource,signal
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(25,25));signal.alarm(55)
from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime
L=Path(__file__).parent;S=L/'sources';S.mkdir(exist_ok=True);logs=[]
items=[('axiom-solution.lean','https://raw.githubusercontent.com/AxiomMath/gdm-formal-conjectures/main/BorweinSineSeries/solution.lean'),('axiom-doc.md','https://raw.githubusercontent.com/AxiomMath/gdm-formal-conjectures/main/docs/BorweinSineSeries.md'),('openai.html','https://github.com/openai/math'),('aim.html','https://github.com/MColbrook/AI-for-Mathematics'),('count.html','https://github.com/Count-Research/Results'),('source-current.html','https://arxiv.org/abs/2603.14548'),('boppana-current.html','https://arxiv.org/abs/2007.11017')]
for name,url in items:
 row=dict(url=url,file=name,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=6) as r:
   data=r.read(5000000);row.update(status=r.status,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(S/name).write_bytes(data)
 except Exception as e:row['error']=str(e)
 logs.append(row)
(L/'http-receipts.json').write_text(json.dumps(logs,indent=2));print(json.dumps(logs,indent=2))
