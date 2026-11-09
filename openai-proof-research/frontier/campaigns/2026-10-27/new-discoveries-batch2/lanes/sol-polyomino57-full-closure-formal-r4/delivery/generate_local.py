import os,resource,signal,json
from pathlib import Path
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,)*2);resource.setrlimit(resource.RLIMIT_CPU,(30,35));signal.alarm(45)
L=Path(__file__).resolve().parent;D=L/'local';D.mkdir(exist_ok=True)
pt=lambda p:'(%d,%d)'%tuple(p)
cells=lambda P:'['+','.join(map(pt,P))+']'
def norm(P):
 x=min(a for a,b in P);y=min(b for a,b in P)
 return tuple(sorted((a-x,b-y) for a,b in P)),(-x,-y)
def nbr(P):return sorted({(x+dx,y+dy) for x,y in P for dx,dy in [(1,0),(-1,0),(0,1),(0,-1)]}-set(P))
for size in [7,8,9,10]:
 rows=[tuple(map(tuple,json.loads(s))) for s in (L/'data'/('layer%d.jsonl'%size)).read_text().splitlines()]
 for count in [8,32,128]:
  name='Local%dN%d'%(size,count)
  s=['import FamilyAssembly','set_option autoImplicit false','set_option maxRecDepth 65536','set_option maxHeartbeats 10000000','namespace Polyomino57']
  for j,P in enumerate(rows[len(rows)//2:len(rows)//2+count]):
   nm=name+'r%d'%j;edges=nbr(P);ts=[norm(set(P)|{b}) for b in edges]
   s+=['def '+nm+' : List GridPoint := '+cells(P),'def '+nm+'targets : Array (List GridPoint) := #['+','.join(cells(Q) for Q,t in ts)+']','def '+nm+'choice (b : GridPoint) : ℕ × GridPoint := ((['+','.join('('+pt(b)+',('+str(i)+','+pt(t)+'))' for i,(b,(Q,t)) in enumerate(zip(edges,ts)))+'] : List (GridPoint × (ℕ × GridPoint))).lookup b).getD (0,(0,0))','theorem '+nm+'_checked : successorFastRowCheck '+nm+'targets '+nm+' '+nm+'choice = true := by decide']
  s+=['end Polyomino57'];(D/(name+'.lean')).write_text('\n'.join(s)+'\n')
