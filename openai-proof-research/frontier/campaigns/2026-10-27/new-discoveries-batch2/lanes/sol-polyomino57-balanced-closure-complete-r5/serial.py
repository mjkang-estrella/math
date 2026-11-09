# DEPRECATED historical coordinator; use bounded_build.py and tool-level serial orchestration.
from pathlib import Path
import subprocess,json,sys,os
L=Path(__file__).resolve().parent
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
def run(args):
 q=subprocess.run(args,cwd=L)
 if q.returncode:sys.exit(q.returncode)
for size in map(int,sys.argv[1:]):
 run(['python3','driver.py','trees',str(size)])
 run(['python3','driver.py','trees',str(size+1)])
 n=sum(1 for _ in (L/'data'/f'layer{size}.jsonl').open())
 for start in range(0,n,32):
  name=f'C{size}R{start:05d}'
  if not (L/'work'/(name+'.lean')).exists():run(['python3','generate.py','batch',str(size),str(start),'32'])
  run(['python3','driver.py',name])
 print('STAGE ROWS COMPLETE',size,flush=True)
