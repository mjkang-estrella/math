import os,resource,signal,time,json,urllib.request,urllib.error,hashlib,sys
from pathlib import Path
from datetime import datetime,timezone
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU,(45,45));signal.alarm(55)
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
b=Path(__file__).resolve().parent
receipts=json.loads((b/'http.json').read_text()) if (b/'http.json').exists() else []
blocked=set(r['url'].split('/')[2] for r in receipts if r.get('status') in [403,429] or r.get('challenge'))
def fetch(n,u):
 host=u.split('/')[2]
 if host in blocked: return None
 r={'file':n,'url':u,'utc':datetime.now(timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Public mathematical research'}),timeout=20) as f:
   data=f.read(15000000);r['status']=f.status
  if len(data)==15000000:raise RuntimeError('download cap; not complete')
  if b'anubis' in data[:15000].lower() or b'just a moment' in data[:3000].lower():r['challenge']=True;blocked.add(host)
  (b/'sources'/n).write_bytes(data);r.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
 except urllib.error.HTTPError as e:
  r['status']=e.code;r['error']=str(e)
  if e.code in [403,429]:blocked.add(host)
 except Exception as e:r['error']=repr(e)
 receipts.append(r);(b/'http.json').write_text(json.dumps(receipts,indent=2))
 return json.loads(data) if n.endswith('.json') and 'error' not in r else None
if __name__=='__main__':
 for n,u in json.loads(sys.argv[1]):fetch(n,u)
 print(json.dumps(receipts[-10:],indent=2))
