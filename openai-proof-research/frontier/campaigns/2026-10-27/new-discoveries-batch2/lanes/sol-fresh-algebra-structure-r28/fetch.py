import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']: os.environ[k]='1'
import resource,signal,urllib.request,json,datetime,hashlib
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,30));signal.alarm(90)
b=Path(__file__).parent
log=json.loads((b/'http-log.json').read_text()) if (b/'http-log.json').exists() else []
def get(name,url):
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-source-research/1.0'}),timeout=25) as r: data=r.read(16000000); status=r.status
  (b/'sources'/name).write_bytes(data);log.append(dict(url=url,name=name,status=status,utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sha256=hashlib.sha256(data).hexdigest()))
 except Exception as e: log.append(dict(url=url,name=name,error=str(e),utc=datetime.datetime.now(datetime.timezone.utc).isoformat()))
 (b/'http-log.json').write_text(json.dumps(log,indent=2))
if __name__=='__main__':
 get('evolution.html','https://arxiv.org/html/2512.12418v1')
 get('evolution-abs.html','https://arxiv.org/abs/2512.12418')
