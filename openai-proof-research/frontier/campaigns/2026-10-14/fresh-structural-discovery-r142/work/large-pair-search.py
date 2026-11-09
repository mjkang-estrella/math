from pathlib import Path
from itertools import product
import runpy,json,random,time
R=Path(__file__).resolve().parents[1];f=runpy.run_path(str(R/'packet/public/interval_betti.py'))['interval_betti'];rng=random.Random(1420142)
def setup(box):
 n=len(box);E=sorted(product(*(range(a) for a in box)),key=lambda u:(sum(u),u));lower={}
 for u in E:
  V={u}
  for i in range(n):
   if u[i]:V|=lower[tuple(u[j]-(i==j) for j in range(n))]
  for i in range(n):
   for j in range(i+1,n):
    if u[i] and u[j]+1<box[j]:V|=lower[tuple(u[k]-(i==k)+(j==k) for k in range(n))]
  lower[u]=V
 bydeg=[[u for u in E if sum(u)==d] for d in range(sum(box)-n+1)]
 def lex(A):
  C=set()
  for row in bydeg:C.update(row[:sum(u in A for u in row)])
  return frozenset(C)
 return E,lower,lex
start=time.monotonic();out=[]
for box in [(2,)*7,(3,)*4,(2,3,4,5),(3,3,3,4)]:
 E,lower,lex=setup(box);found=None;limit=False
 for trial in range(1200):
  seeds=rng.sample(E,rng.randint(1,min(15,len(E))));A=frozenset().union(*(lower[u] for u in seeds))
  seeds2=rng.sample(sorted(A),rng.randint(0,min(15,len(A))));B=frozenset().union(*(lower[u] for u in seeds2))
  a=f(A,B,box);b=f(lex(A),lex(B),box)
  if any(v>b.get(k,0) for k,v in a.items()):
   found=dict(A=sorted(A),B=sorted(B),D=sorted(A-B),L=sorted(lex(A)-lex(B)),beta={str(k):v for k,v in a.items()},lex_beta={str(k):v for k,v in b.items()});break
  if time.monotonic()-start>45:limit=True;break
 o=dict(box=box,trials=trial+1,seed=1420142,found=found,time_limit=limit);out.append(o);print(json.dumps(o),flush=True)
 if found or limit:break
(R/'packet/private/large-pair-search.json').write_text(json.dumps(out,indent=2))
