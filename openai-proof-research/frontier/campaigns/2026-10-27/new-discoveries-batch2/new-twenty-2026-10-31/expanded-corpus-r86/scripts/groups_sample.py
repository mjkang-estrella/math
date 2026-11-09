import itertools,collections,random,json
from pathlib import Path
L=Path(__file__).resolve().parents[1];P=1000003; dirs=[(1,0),(0,1),(-1,0),(0,-1)]
def detpoly(T,ix):
 ans=collections.Counter()
 for perm in itertools.permutations(ix):
  sign=(-1)**sum(perm[a]>perm[b] for a in range(len(ix)) for b in range(a+1,len(ix)))
  terms=[(0,0,0,sign)]
  for i,j in zip(ix,perm):
   new=[]
   for t,x,y,c in terms:
    if i==j:new.append((t,x,y,c))
    if T[i][j]:new.append((t+1,x+dirs[j][0],y+dirs[j][1],-c))
   terms=new
  for t,x,y,c in terms:ans[t,x,y]+=c
 return {k:v for k,v in ans.items() if v}
def coeff(poly,axis,other,t):
 c=[0,0,0]
 for (e,a,b),v in poly.items():
  exp=a if axis==0 else b;o=b if axis==0 else a
  c[exp+1]=(c[exp+1]+v*pow(t,e,P)*pow(other,o,P))%P
 return c
def invol(D,M,axis,x,y,t):
 z=x if axis==0 else y;other=y if axis==0 else x
 a=coeff(D,axis,other,t);b=coeff(M,axis,other,t)
 av=sum(a[i]*pow(z,i,P) for i in range(3))%P;bv=sum(b[i]*pow(z,i,P) for i in range(3))%P
 den=(a[2]*bv-av*b[2])*z%P;num=(a[0]*bv-av*b[0])%P
 if den==0:raise ZeroDivisionError
 z2=num*pow(den,-1,P)%P
 if z2==0:raise ZeroDivisionError
 return (z2,y) if axis==0 else (x,z2)
def conn(T):
 for i in range(4):
  s={i}
  for _ in range(4):s|={j for a in list(s) for j in range(4) if T[a][j]}
  if len(s)<4:return False
 return True
rng=random.Random(86);rules=[]
while len(rules)<128:
 T=[[int(i==j or rng.randrange(2)) for j in range(4)] for i in range(4)]
 # all loops imply U and D; Ten or Tne excludes glued; strong connectivity from Sec2
 if conn(T) and (T[0][1] or T[1][0]) and T not in rules:rules.append(T)
rows=[]
for idx,T in enumerate(rules):
 D=detpoly(T,list(range(4)));Ms=[detpoly(T,[j for j in range(4) if j!=i]) for i in range(4)];orders=[]
 for M in Ms:
  o=[]
  for start in [(7,11,5),(13,17,19)]:
   x,y,t=start;found=None
   try:
    for k in range(1,25):
     x,y=invol(D,M,0,x,y,t);x,y=invol(D,M,1,x,y,t)
     if (x,y)==start[:2]:found=k;break
   except ZeroDivisionError:found='singular'
   o.append(found)
  orders.append(o)
 row={'index':idx,'T':T,'product_orders_at_two_points_cutoff24':orders};rows.append(row);print(json.dumps(row),flush=True)
(L/'outputs/groups-check.json').write_text(json.dumps({'prime':P,'seed':86,'scope':'128 distinct strongly connected rules with all loops; Ten or Tne; exact modular diagnostics only, no rational order certificate','rows':rows},indent=2))
