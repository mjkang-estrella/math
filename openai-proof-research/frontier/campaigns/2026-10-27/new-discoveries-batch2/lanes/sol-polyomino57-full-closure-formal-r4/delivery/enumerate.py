import os,resource,signal,json,time
from pathlib import Path
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(120,125));signal.alarm(150)
L=Path(__file__).resolve().parent;D=L/'data';D.mkdir(exist_ok=True)
def norm(P):
 x=min(a for a,b in P);y=min(b for a,b in P)
 return tuple(sorted((a-x,b-y) for a,b in P))
def nbr(P):return {(x+dx,y+dy) for x,y in P for dx,dy in [(1,0),(-1,0),(0,1),(0,-1)]}-set(P)
rows=[((0,0),)]
for n in range(1,12):
 t=time.monotonic()
 if n>1:rows=sorted({norm(set(P)|{b}) for P in rows for b in nbr(P)})
 with (D/('layer%d.jsonl'%n)).open('w') as f:
  for P in rows:f.write(json.dumps(P,separators=(',',':'))+'\n')
 print(n,len(rows),time.monotonic()-t,resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,flush=True)
