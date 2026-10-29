import resource,signal,os
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']:os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(55)
import urllib.request,urllib.error,hashlib,datetime,json,pathlib
L=pathlib.Path(__file__).parent;rows=[]
for name,url in [('current-arxiv.html','https://arxiv.org/abs/2603.14548'),('current-mathdb.json','https://mathdb.com/api/posts/373621'),('companion.html','https://www.researchgate.net/publication/402805374_THE_IRRATIONALITY_MEASURE_AND_DIOPHANTINE_CONSTRAINTS_ON_p_BEYOND_THE_BORWEIN-BAILEY-GIRGENSOHN_SINUSOIDAL_SERIES')]:
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':name}
 try:
  with urllib.request.urlopen(url,timeout=12) as f:
   r.update(status=f.status,final_url=f.url);data=f.read(3000000)
  (L/'sources'/name).write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest();r['bytes']=len(data)
 except Exception as e:r['error']=str(e)
 rows.append(r)
(L/'http-log.json').write_text(json.dumps(rows,indent=2));print(json.dumps(rows,indent=2))
