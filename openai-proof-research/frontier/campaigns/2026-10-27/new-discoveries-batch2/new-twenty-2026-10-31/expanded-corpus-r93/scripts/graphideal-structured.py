# Structured continuation, using the exact same squarefree-colon and GF(2) homology engine.
import sys,json,itertools,random
from pathlib import Path
# Import without executing the CLI block.
src=Path(__file__).with_name('graphideal.py').read_text().split('rng=random.Random')[0]
exec(compile(src,'graphideal-core','exec'))
res=[]
def run(name,n,es):
 nb=[1<<i for i in range(n)]
 for a,b in es:nb[a]|=1<<b;nb[b]|=1<<a
 v,r=invariants(nb);print(name,n,v,r,flush=True)
 res.append([name,n,v,r]);(D/'outputs/graphideal-structured.json').write_text(json.dumps(res))
 if v>r:print('WITNESS',name,n,nb,v,r,flush=True)
for n in range(4,14):
 cyc=[(i,(i+1)%n) for i in range(n)]
 run('cycle',n,cyc)
 run('anticycle',n,[(i,j) for i in range(n) for j in range(i+1,n) if (j-i) not in (1,n-1)])
 run('wheel',n,[(i,(i+1)%(n-1)) for i in range(n-1)]+[(i,n-1) for i in range(n-1)])
# Petersen and line graph of K5.
es=[(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+[(i+5,(i+2)%5+5) for i in range(5)]
run('Petersen',10,es)
verts=list(itertools.combinations(range(5),2));run('lineK5',10,[(i,j) for i in range(10) for j in range(i+1,10) if set(verts[i])&set(verts[j])])
