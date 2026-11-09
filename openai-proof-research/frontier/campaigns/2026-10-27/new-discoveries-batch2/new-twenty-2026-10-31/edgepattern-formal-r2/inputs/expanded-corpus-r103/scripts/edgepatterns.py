from pathlib import Path
import itertools as it,functools as ft,json,random,warnings
from fractions import Fraction as F
import numpy as np
from scipy.optimize import linprog
warnings.filterwarnings('ignore',category=Warning)
D=Path(__file__).resolve().parents[1];rng=random.Random(103)
def stats(adj,lay):
 n=len(adj)
 @ft.lru_cache(None)
 def rec(mask):
  if not mask:return (0,1,(0,0,0))
  # Component splitting to avoid exponential product.
  first=mask&-mask;reach=first;front=first
  while front:
   v=front&-front;front-=v;new=adj[v.bit_length()-1]&mask&~reach;reach|=new;front|=new
  if reach!=mask:
   a,c,x=rec(reach);b,d,y=rec(mask^reach)
   return a+b,c*d,tuple(x[i]*d+y[i]*c for i in range(3))
  v=max((i for i in range(n) if mask>>i&1),key=lambda i:(adj[i]&mask).bit_count());bit=1<<v
  a,c,x=rec(mask^bit);b,d,y=rec(mask&~(adj[v]|bit));b+=1;y=list(y);y[lay[v]]+=d;y=tuple(y)
  if a>b:return a,c,x
  if b>a:return b,d,y
  return a,c+d,tuple(x[i]+y[i] for i in range(3))
 a,c,x=rec((1<<n)-1);return tuple(F(v,c) for v in x)
def make(L,R):
 adj=[0,0];lay=[0,0];leaves=[[],[]]
 def edge(a,b):adj[a]|=1<<b;adj[b]|=1<<a
 edge(0,1)
 for root,seq in enumerate([L,R]):
  for k in seq:
   a=len(adj);adj.append(0);lay.append(1);edge(root,a)
   for _ in range(k):b=len(adj);adj.append(0);lay.append(2);edge(a,b);leaves[root].append(b)
 return adj,lay,leaves
rows=[]
for d in [3,4,5,6]:
 types=list(it.combinations_with_replacement(range(d),d-1));ts=set()
 for i,L in enumerate(types):
  for R in types[i:]:
   adj,lay,_=make(L,R);ts.add(stats(adj,lay))
 T=sorted(ts);A=np.array([[float(v) for v in t] for t in T]).T;fails=[]
 for trial in range(600):
  L=[rng.randrange(d) for _ in range(d-1)];R=[rng.randrange(d) for _ in range(d-1)];adj,lay,leaves=make(L,R)
  pairs=list(it.product(*leaves));rng.shuffle(pairs);added=0
  for a,b in pairs:
   if rng.random()>.25 or adj[a].bit_count()>=d or adj[b].bit_count()>=d:continue
   # Any path of length <=3 gives a short cycle; bipartiteness rules out odd cycles.
   reach=(1<<a);front=reach
   for _ in range(3):
    new=0
    while front:v=front&-front;front-=v;new|=adj[v.bit_length()-1]
    front=new&~reach;reach|=new
   if reach>>b&1:continue
   adj[a]|=1<<b;adj[b]|=1<<a;added+=1
  if not added:continue
  e=stats(adj,lay)
  r=linprog(np.zeros(len(T)),A_ub=A,b_ub=[float(v) for v in e],A_eq=np.ones((1,len(T))),b_eq=[1],bounds=(0,None),method='highs',options={'threads':1})
  if r.status!=0:
   fails.append(dict(d=d,L=L,R=R,adj=adj,layers=lay,e=[str(v) for v in e],status=r.status));print('FAIL',fails[-1],flush=True);break
 rows.append(dict(d=d,tree_half_types=len(types),distinct_tree_constraints=len(T),trials=600,failures=fails))
 (D/'outputs/edgepatterns.json').write_text(json.dumps(rows,indent=2)+'\n');print('RESULT',rows[-1],flush=True)
 if fails:break
