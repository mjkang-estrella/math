import urllib.request,urllib.error,hashlib,json,datetime,resource,sys,os
from pathlib import Path
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(25,25))
b=Path(__file__).parent
records=json.loads((b/'http.json').read_text()) if (b/'http.json').exists() else []
name,url=sys.argv[1:];r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
try:
 with urllib.request.urlopen(url,timeout=25) as f:
  d=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(d).hexdigest(),bytes=len(d));(b/'sources'/name).write_bytes(d)
 if any(t in d[:10000].lower() for t in (b'incapsula',b'captcha',b'anubis')):r['challenge']='STOP affected route'
except Exception as e:r['error']=str(e)
records.append(r);(b/'http.json').write_text(json.dumps(records,indent=2));print(r)
