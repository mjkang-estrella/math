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
def unbounded(T,need,exclude):
 allowed=[i for i in range(4) if i!=exclude];reach=[[bool(T[i][j]) for j in range(4)] for i in range(4)]
 for k in allowed:
  for i in allowed:
   for j in allowed:reach[i][j]|=reach[i][k] and reach[k][j]
 return reach[need][need]
def prod(T,edges):
 return all(T[i][j] for i,j in edges)
def diagonal(T):
 specs=[[(1,1)],[(2,2)],[(1,2),(2,1)],[(1,0),(0,2),(2,1)],[(1,2),(2,0),(0,1)],[(2,1),(1,3),(3,2)],[(2,3),(3,1),(1,2)]]
 specs2=[[(0,0)],[(3,3)],[(0,3),(3,0)],[(0,1),(1,3),(3,0)],[(0,3),(3,1),(1,0)],[(3,0),(0,2),(2,3)],[(3,2),(2,0),(0,3)]]
 specs3=[[(0,0)],[(1,1)],[(1,0),(0,1)],[(0,1),(1,3),(3,0)],[(0,3),(3,1),(1,0)],[(1,0),(0,2),(2,1)],[(1,2),(2,0),(0,1)]]
 return all(any(prod(T,edges) for edges in sp) for sp in [specs,specs2,specs3])
rules=[];counts=collections.Counter()
for mask in range(65536):
 T=[[(mask>>(4*i+j))&1 for j in range(4)] for i in range(4)]
 if not conn(T):continue
 counts['connected']+=1
 if not all(unbounded(T,i,(i+2)%4) for i in range(4)):continue
 counts['U']+=1
 if not diagonal(T):continue
 counts['UD']+=1
 if not (T[0][1] or T[0][0]*T[0][2]*T[2][1] or T[1][0] or T[1][1]*T[1][3]*T[3][0]):continue
 counts['Q']+=1;rules.append(T)
print('COUNTS',dict(counts),flush=True)
assert counts['Q']==13749 and counts['UD']==14209 and counts['U']==14978
import sys
slice_start=int(sys.argv[1]) if len(sys.argv)>1 else 0
stop=int(sys.argv[2]) if len(sys.argv)>2 else len(rules)
rules=rules[slice_start:stop]
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
(L/f'outputs/groups-check-{slice_start}-{stop}.json').write_text(json.dumps({'prime':P,'counts':dict(counts),'scope':'All Q rules in stated slice; exact modular diagnostics only, no rational order certificate','rows':rows},indent=2))
