from pathlib import Path
import os,resource,signal,ast,json,hashlib,time
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(45)
L=Path(__file__).resolve().parent;t0=time.monotonic();lookup={};count=0
def norm(P):
 x=min(a for a,b in P);y=min(b for a,b in P)
 return tuple((a-x,b-y) for a,b in P),(x,y)
for p in sorted((L/'certificate/formal').glob('Terminal[0-9][0-9][0-9].lean')):
 for line in p.read_text().splitlines():
  if not line.startswith('def Terminal') or ' : List ' not in line:continue
  name=line.split()[1];rows=ast.literal_eval(line.split(' := ',1)[1])
  for i,(P,shift) in enumerate(rows):
   key,corner=norm(P)
   assert key not in lookup,(name,i)
   lookup[key]=(name,i,corner,shift);count+=1
D=L/'terminal-correspondence.jsonl'
with D.open('w') as f:
 for j,line in enumerate((L/'data/layer11.jsonl').open()):
  P=tuple(map(tuple,json.loads(line)));name,i,corner,shift=lookup.pop(P)
  f.write(json.dumps(dict(generated_index=j,forest_chunk=name,chunk_index=i,raw_to_generated=[-corner[0],-corner[1]],generated_placement=[shift[0]+corner[0],shift[1]+corner[1]]),separators=(',',':'))+'\n')
assert not lookup
(L/'terminal-map-receipt.json').write_text(json.dumps(dict(status='DATA_ONLY_NOT_KERNEL_PROOF',supplied_rows=count,generated_rows=j+1,all_supplied_used=True,sha256=hashlib.sha256(D.read_bytes()).hexdigest(),seconds=time.monotonic()-t0,peak_rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss),indent=2)+'\n')
