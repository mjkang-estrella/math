from itertools import product,permutations
from pathlib import Path
import json
D=Path(__file__).resolve().parents[1]
def orders(n):
 out=set()
 for k in range(1,n+1):
  for a in product(range(k),repeat=n):
   if set(a)!=set(range(k)):continue
   multi=[v for v in range(k) if a.count(v)>1]
   for types in product([0,1],repeat=len(multi)):
    b=dict(zip(multi,types));r=tuple(sum(1<<j for j in range(n) if i==j or a[i]<a[j] or (a[i]==a[j] and b.get(a[i],0))) for i in range(n));out.add(r)
 return list(out)
def connected(s,adj):
 if not s:return False
 seen=s&-s
 while True:
  t=seen
  for i in range(len(adj)):
   if seen>>i&1:t|=adj[i]&s
  if t==seen:return seen==s
  seen=t
rows=[]
for n in range(1,6):
 edges=[(i,j) for i in range(n) for j in range(i)];seen=set();ordersn=orders(n)
 for mask in range(1<<len(edges)):
  adj=[0]*n
  for b,(i,j) in enumerate(edges):
   if mask>>b&1:adj[i]|=1<<j;adj[j]|=1<<i
  if n>1 and not connected((1<<n)-1,adj):continue
  canon=min(tuple(adj[p[i]]>>p[j]&1 for i in range(n) for j in range(n)) for p in permutations(range(n)))
  if canon in seen:continue
  seen.add(canon)
  c={s:connected(s,adj) for s in range(1,1<<n)}
  O=[r for r in ordersn if all(c[s] for s in r)]
  # Only connected graphs: root set is full type A; biclosure = relation and complement transitive.
  up=[]
  for r in O:up.append(sum(1<<j for j,s in enumerate(O) if all(x&y==x for x,y in zip(r,s))))
  U=set(up);bad=None
  for i,a in enumerate(up):
   for j in range(i):
    if a&up[j] not in U:bad=(i,j);break
   if bad:break
  row=dict(n=n,edges=[e for b,e in enumerate(edges) if mask>>b&1],ornamentations=len(O),join_failure=bad)
  if bad:row['witness']=[O[x] for x in bad]
  rows.append(row);print(row,flush=True)
  (D/'outputs/lattice.json').write_text(json.dumps(rows,indent=2))
  if bad:raise SystemExit
