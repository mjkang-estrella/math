import itertools,math,json,time
from pathlib import Path
D=Path(__file__).resolve().parents[1];rows=[]
def check(name,els,mul):
 n=len(els);idx={x:i for i,x in enumerate(els)};T=[[idx[mul(a,b)] for b in els] for a in els];orders=[]
 for i in range(n):
  j=i;k=1
  while j: j=T[j][i];k+=1
  orders.append(k)
 def close(H):
  H=set(H)
  while True:
   J=H|{T[a][b] for a in H for b in H}
   if J==H:return frozenset(H)
   H=J
 subs={frozenset({0})};todo=list(subs)
 while todo:
  H=todo.pop()
  for g in range(n):
   if g in H:continue
   J=close(H|{g})
   if J not in subs:subs.add(J);todo.append(J)
 S=sum(sum(orders[g]==math.lcm(*(orders[h] for h in H)) for g in H) for H in subs);cyc=max(orders)==n
 rows.append(dict(name=name,order=n,subgroups=len(subs),S=S,cyclic=cyc,claim_holds=S>=n and ((S==n)==cyc)))
for mods in [(n,) for n in range(1,17)]+[(2,2),(2,4),(2,8),(4,4),(2,2,2),(2,2,2,2),(3,3)]:
 check('x'.join('C'+str(m) for m in mods),list(itertools.product(*(range(m) for m in mods))),lambda a,b:tuple((a[i]+b[i])%m for i,m in enumerate(mods)))
for m in [4,8,16]:check('Dihedral'+str(2*m),list(itertools.product(range(2),range(m))),lambda a,b:((a[0]+b[0])%2,(a[1]+(-1)**a[0]*b[1])%m))
(D/'outputs/group-search.json').write_text(json.dumps({'rows':rows,'scope':'explicit cyclic, abelian product and dihedral 2-group families; no all-small-groups claim; exact subgroup closure and maximal-order totient'},indent=2));print(json.dumps(rows))
