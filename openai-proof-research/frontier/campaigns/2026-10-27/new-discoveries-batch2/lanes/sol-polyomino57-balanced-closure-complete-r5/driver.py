# DEPRECATED historical coordinator; use bounded_build.py and tool-level serial orchestration.
from pathlib import Path
import subprocess,json,sys,os,hashlib
L=Path(__file__).resolve().parent;W=L/'work'
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
def build(m):
 p=W/(m+'.lean');out=W/(m+'.olean')
 if out.exists() and out.stat().st_mtime>p.stat().st_mtime:return
 q=subprocess.run(['python3',str(L/'run.py'),'-o',m+'.olean',m+'.lean'],cwd=W,capture_output=True,text=True)
 (L/'logs').mkdir(exist_ok=True);(L/'logs'/(m+'.log')).write_text(q.stdout+q.stderr)
 print(m,q.returncode,flush=True)
 if q.returncode:sys.exit(q.returncode)
 with (L/'built-source-receipts.jsonl').open('a') as f:
  f.write(json.dumps(dict(module=m,source_sha256=hashlib.file_digest(p.open('rb'),'sha256').hexdigest(),olean_sha256=hashlib.file_digest(out.open('rb'),'sha256').hexdigest()))+'\n')
if sys.argv[1]=='trees':
 for m in json.loads((L/'tree-modules.json').read_text()):
  if len(sys.argv)<3 or m.startswith('F'+sys.argv[2]):build(m)
else:
 build(sys.argv[1])
queue=L/'queue.json'
if queue.exists():
 pending=json.loads(queue.read_text());queue.unlink()
 for m in pending:build(m)
for size in [7,8,9,10]:
 stage=W/f'Stage{size}Closed.olean'
 if stage.exists():continue
 n=sum(1 for _ in (L/'data'/f'layer{size}.jsonl').open())
 if all((W/f'C{size}R{k:05d}.olean').exists() for k in range(0,n,32)):
  for m in json.loads((L/'aggregation-modules.json').read_text()):
   if m.startswith(f'F{size}B') or m==f'Stage{size}Closed':build(m)

if (L/"stop_serial").exists():
 import signal
 os.kill(os.getppid(),signal.SIGTERM)
