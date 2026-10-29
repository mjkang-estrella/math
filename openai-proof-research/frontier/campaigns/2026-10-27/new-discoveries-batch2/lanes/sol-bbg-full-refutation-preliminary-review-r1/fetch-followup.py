import os,resource,signal
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(25,25));signal.alarm(55)
from pathlib import Path
import urllib.request,urllib.error,json,hashlib,datetime
L=Path(__file__).parent;S=L/'sources';S.mkdir(exist_ok=True);logs=[]
items=[('aim-current.html','https://github.com/MColbrook/AIM'),('count-current.html','https://github.com/suvrit/count-ex-machina'),('omega-current.html','https://github.com/the-omega-institute/trureturing'),('openai-README.md','https://raw.githubusercontent.com/openai/math/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/README.md'),('aim-README.md','https://raw.githubusercontent.com/MColbrook/AIM/8729eab98bafe409b66c5e39253bf56569a62327/README.md'),('count-README.md','https://raw.githubusercontent.com/suvrit/count-ex-machina/dbf673741a54c7dc9d88a6aec0e8148a538f4a3a/README.md'),('mo409550.html','https://mathoverflow.net/questions/409550/convergence-of-the-series-sum-n-1-infty-frac2-sin-nn3n-na-for')]
for name,url in items:
 row=dict(url=url,file=name,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(url,timeout=6) as r:
   data=r.read(5000000);row.update(status=r.status,bytes=len(data),sha256=hashlib.sha256(data).hexdigest());(S/name).write_bytes(data)
 except Exception as e:row['error']=str(e)
 logs.append(row)
(L/'http-followup.json').write_text(json.dumps(logs,indent=2));print(json.dumps(logs,indent=2))
