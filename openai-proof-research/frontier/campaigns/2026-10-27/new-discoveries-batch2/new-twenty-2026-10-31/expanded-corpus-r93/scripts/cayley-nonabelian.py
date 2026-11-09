import itertools,json,functools,sys
from pathlib import Path
D=Path(__file__).resolve().parents[1]
def prime(rows):
 n=len(rows)
 for b in range(1,n):
  mod={0,b};change=True
  while change:
   change=False
   for v in range(n):
    if v in mod:continue
    if len({((rows[v]>>u)&1,(rows[u]>>v)&1) for u in mod})>1:mod.add(v);change=True
  if len(mod)<n:return False
 return True
def cyclepower(rows,k):
 n=len(rows);succ=[[w for w in range(n) if v!=w and rows[v]&~rows[w]==1<<w] for v in range(n)]
 def rec(path):
  if len(path)==n:return 0 in succ[path[-1]] and all(rows[path[i]]==sum(1<<path[(i+j)%n] for j in range(1,k+1)) for i in range(n))
  return any(rec(path+[w]) for w in succ[path[-1]] if w not in path)
 return rec([0])
kind=sys.argv[1];
if kind=='F21':
 elems=list(itertools.product(range(7),range(3)))
 def mul(a,b):return ((a[0]+pow(2,a[1],7)*b[0])%7,(a[1]+b[1])%3)
elif kind=='H27':
 elems=list(itertools.product(range(3),repeat=3))
 def mul(a,b):return ((a[0]+b[0])%3,(a[1]+b[1])%3,(a[2]+b[2]+a[0]*b[1])%3)
else:
 # Generalized quaternion Q_4m, x^(2m)=1, y²=x^m, yx=x^-1 y.
 m=int(kind[1:])//4;elems=list(itertools.product(range(2*m),range(2)))
 def mul(a,b):return ((a[0]+(-1)**a[1]*b[0]+m*a[1]*b[1])%(2*m),(a[1]+b[1])%2)
n=len(elems);idx={a:i for i,a in enumerate(elems)};table=[[idx[mul(a,b)] for b in elems] for a in elems];inv=[next(j for j in range(n) if table[i][j]==0) for i in range(n)];pairs=[(i,inv[i]) for i in range(1,n) if i<inv[i]];tight=0;primecnt=0;candidates=[];total=0
for cs in itertools.product(range(3),repeat=len(pairs)):
 S=[pairs[j][c-1] for j,c in enumerate(cs) if c];k=len(S);total+=1
 sec={table[a][b] for a in S for b in S}-set(S)-{0}
 if len(sec)!=k:continue
 tight+=1
 if k<2 or n==2*k+1:continue
 rows=tuple(sum(1<<table[v][s] for s in S) for v in range(n))
 if not prime(rows):continue
 primecnt+=1
 if not cyclepower(rows,k):candidates.append(S);print('CANDIDATE',kind,S,flush=True)
 if total%10000==0:print('progress',total,tight,primecnt,flush=True)
print('COMPLETE',kind,n,total,tight,primecnt,candidates,flush=True)
(D/f'outputs/cayley-{kind}.json').write_text(json.dumps({'group':kind,'n':n,'tested':total,'tight':tight,'prime_nontrivial_nontournament':primecnt,'candidates':candidates}))
