from pathlib import Path
from itertools import combinations
import random,json
P=Path(__file__).resolve().parent

def dist(n,E):
 d=[[0 if i==j else 999 for j in range(n)] for i in range(n)]
 for i,j in E:d[i][j]=d[j][i]=1
 for k in range(n):
  for i in range(n):
   for j in range(n):d[i][j]=min(d[i][j],d[i][k]+d[k][j])
 return d

def line(d,a,b):
 return sum(1<<x for x in range(len(d)) if d[a][b]==d[a][x]+d[x][b] or d[a][b]==abs(d[a][x]-d[b][x]))
def gp(d,S):return all(max(d[a][b],d[a][c],d[b][c])*2!=d[a][b]+d[a][c]+d[b][c] for a,b,c in combinations(S,3))
def terminal(d,S):return gp(d,S) and all(any(abs(d[u][a]-d[u][b])==d[a][b] for a,b in combinations(S,2)) for u in range(len(d)) if u not in S)
def lower(d):
 n=len(d);full=(1<<n)-1;L={(a,b):line(d,a,b) for a,b in combinations(range(n),2)}
 for k in range(2,n+1):
  for S in combinations(range(n),k):
   if not gp(d,S):continue
   m=sum(1<<x for x in S)
   for a,b in combinations(S,2):m|=L[a,b]
   if m==full:return k,S

def product(d,e):return [[d[a][b]+e[x][y] for b in range(len(d)) for y in range(len(e))] for a in range(len(d)) for x in range(len(e))]
def small_maximals(d):
 n=len(d);F=(1<<n)-1;L=[[0]*n for _ in range(n)]
 for a,b in combinations(range(n),2):L[a][b]=L[b][a]=line(d,a,b)
 for a,b in combinations(range(n),2):
  if L[a][b]==F:return (a,b)
 for a,b,c in combinations(range(n),3):
  if (L[a][b]>>c)&1:continue
  if L[a][b]|L[a][c]|L[b][c]==F:return (a,b,c)
 return None
# Exact all-coordinate synchronized rectangle identity, not a proof of conjecture.
d=dist(3,[(0,1),(1,2)]);D=product(d,d);rect_checks=0
for a,b in combinations(range(9),2):
 ag,ah=divmod(a,3);bg,bh=divmod(b,3)
 for z in range(9):
  x,y=divmod(z,3)
  inside=d[ag][bg]==d[ag][x]+d[x][bg] and d[ah][bh]==d[ah][y]+d[y][bh]
  enda=d[x][bg]==d[x][ag]+d[ag][bg] and d[y][bh]==d[y][ah]+d[ah][bh]
  endb=d[x][ag]==d[x][bg]+d[bg][ag] and d[y][ah]==d[y][bh]+d[bh][ah]
  assert bool((line(D,a,b)>>z)&1)==(inside or enda or endb);rect_checks+=1
S=[2,3,7];assert gp(D,S);assert not gp(d,[0,1,2])
# Extending diameter-three clique scheme beyond its scope fails on C8 singleton blocks.
c8=dist(8,[(i,(i+1)%8) for i in range(8)]);assert not gp(c8,[0,2,4]);assert c8[0][4]==c8[0][2]+c8[2][4]
c6=dist(4,[(0,1),(0,2),(0,3)]);maxsets=[s for k in range(5) for s in combinations(range(4),k) if gp(c6,s)];M=max(map(len,maxsets));assert M==3;assert not any(terminal(c6,s) for s in maxsets if len(s)==M);assert terminal(c6,(0,1))
# Fresh bounded exact product search; every searched factor lower number certified by exhaustive subsets.
rng=random.Random(101);graphs=[];attempts=0
while len(graphs)<16 and attempts<500:
 attempts+=1;n=7+(attempts%4);p=[.68,.78,.88,.94][attempts%4];E=[e for e in combinations(range(n),2) if rng.random()<p];d=dist(n,E)
 if max(map(max,d))==999:continue
 k,w=lower(d)
 if k>=4:graphs.append(dict(n=n,E=E,d=d,lower=k,witness=w))
results=[]
for i,g in enumerate(graphs):
 h=graphs[(i+3)%len(graphs)];D=product(g['d'],h['d']);w=small_maximals(D)
 results.append(dict(i=i,j=(i+3)%len(graphs),orders=[g['n'],h['n']],factor_lower=[g['lower'],h['lower']],product_order=len(D),maximal_at_most3=w))
 if w is not None:break
out=dict(rectangle_checks=rect_checks,projection_obstruction=dict(graph='P3 square P3',S=[divmod(x,3) for x in S],projection=[0,1,2]),diameter_extension_obstruction=dict(graph='C8',blocks=[[0],[2],[4]],distances=[2,2,4]),maximum_cardinality_terminal_obstruction=dict(graph='K1,3',gp=M,maximum_sets=[s for s in maxsets if len(s)==M],terminal_pair=[0,1]),attempts=attempts,graphs=graphs,product_search=results,status='bounded diagnostics; full universal result unresolved')
(P/'check-results.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k!='graphs'},indent=2))
