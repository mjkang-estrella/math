import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
import resource,signal,urllib.request,urllib.error,hashlib,json,datetime,sys
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,)*2);signal.alarm(55)
b=Path(__file__).parent;log=json.loads((b/'extra-fetch.json').read_text()) if (b/'extra-fetch.json').exists() else []
blocked={'api.github.com'}|{x['url'].split('/')[2] for x in log if x.get('status') in [403,429]}
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 if url.split('/')[2] in blocked:continue
 row=dict(file=name,url=url,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'source-research/1.0'}),timeout=20) as r:
   data=r.read(16000001);assert len(data)<=16000000;row['status']=r.status
  (b/'sources'/name).write_bytes(data);row['sha256']=hashlib.sha256(data).hexdigest()
 except Exception as e:
  row['error']=str(e);row['status']=getattr(e,'code',None)
  if row['status'] in [403,429]:blocked.add(url.split('/')[2])
 log.append(row);(b/'extra-fetch.json').write_text(json.dumps(log,indent=2))
