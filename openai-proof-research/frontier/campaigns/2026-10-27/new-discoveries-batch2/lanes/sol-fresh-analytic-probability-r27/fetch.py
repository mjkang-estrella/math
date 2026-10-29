import os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:os.environ[k]='1'
import resource,signal,json,urllib.request,datetime,hashlib
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(40,40));signal.alarm(110)
b=Path(__file__).parent;s=b/'sources';log=json.loads((b/'http-log.json').read_text()) if (b/'http-log.json').exists() else []
# Prior explicit API403 at09:05/09:06 is honored: no API retry in this lane.
blocked={'api.github.com'}|{x['url'].split('/')[2] for x in log if x.get('status') in [403,429]}
def get(name,url):
 if url.split('/')[2] in blocked:print('BLOCKED',url);return
 row=dict(url=url,name=name,utc=datetime.datetime.now(datetime.timezone.utc).isoformat())
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'mathematical-source-research/1.0'}),timeout=25) as r:
   data=r.read(12000000);row['status']=r.status
  (s/name).write_bytes(data);row['sha256']=hashlib.sha256(data).hexdigest();print(name,len(data))
 except Exception as e:
  row['error']=str(e);row['status']=getattr(e,'code',None)
  if row['status'] in [403,429]:blocked.add(url.split('/')[2])
 finally:log.append(row);(b/'http-log.json').write_text(json.dumps(log,indent=2))
if __name__=='__main__':
 import sys
 for name,url in zip(sys.argv[1::2],sys.argv[2::2]):get(name,url)
