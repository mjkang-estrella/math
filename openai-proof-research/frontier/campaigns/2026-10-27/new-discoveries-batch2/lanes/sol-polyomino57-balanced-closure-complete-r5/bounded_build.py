from pathlib import Path
import subprocess,json,sys,os,hashlib,resource,signal,time
L=Path(__file__).resolve().parent;W=L/'work';m=sys.argv[1];p=W/(m+'.lean');out=W/(m+'.olean')
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
if out.exists() and out.stat().st_mtime>p.stat().st_mtime:
 print(json.dumps(dict(module=m,status='CACHED_DEVELOPMENT')));sys.exit(0)
q=subprocess.Popen(['python3',str(L/'run.py'),'-o',m+'.olean',m+'.lean'],cwd=W,stdout=subprocess.PIPE,stderr=subprocess.PIPE,text=True)
# Child exists with its independent allowance before the supervisor is capped.
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(225)
a,b=q.communicate();(L/'logs').mkdir(exist_ok=True);(L/'logs'/(m+'.log')).write_text(a+b)
if q.returncode:print(a+b);sys.exit(q.returncode)
r=dict(module=m,status='PASS',source_sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),olean_sha256=hashlib.file_digest(out.open('rb'),'sha256').hexdigest())
with (L/'built-source-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
print(json.dumps(r))
