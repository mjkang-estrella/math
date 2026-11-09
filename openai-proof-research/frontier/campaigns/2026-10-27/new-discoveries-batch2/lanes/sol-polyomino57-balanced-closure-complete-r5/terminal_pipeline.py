# DEPRECATED historical coordinator; use bounded_build.py and tool-level serial orchestration.
from pathlib import Path
import subprocess,sys,json,os
L=Path(__file__).resolve().parent;W=L/'work'
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
def run(args):
 q=subprocess.run(args,cwd=L)
 if q.returncode:sys.exit(q.returncode)
def build(m):run(['python3','driver.py',m])
for start in range(0,sum(1 for _ in (L/'data/layer11.jsonl').open()),32):
 name=f'TR{start:06d}'
 if not (W/(name+'.lean')).exists():run(['python3','terminal_generate.py',str(start),'32'])
 for line in (W/(name+'.lean')).read_text().splitlines():
  if line.startswith('import Terminal'):build(line.split()[1])
 build(name)
for m in json.loads((L/'terminal-aggregation-modules.json').read_text()):build(m)
build('CompleteEndpoint')
print('CLOSED ENDPOINT COMPILED: fresh source-only replay still required',flush=True)
run(['python3','finish.py'])
