import json,datetime,hashlib
from pathlib import Path
import sympy as s
L=Path(__file__).resolve().parent;t=s.Symbol('t')
def stern(m):
 a,b=s.Poly(0,t),s.Poly(1,t)
 for bit in bin(m)[2:]:
  if bit=='0':a,b=a*t,a+b
  else:a,b=a+b,b*t
 return a
def V(k,n):return stern(2**(2*n+k)-3*2**(n+k-1)+2**k-3)
def v2(x):
 x=abs(int(x));return (x&-x).bit_length()-1
def polygon(p):
 hull=[]
 for i in range(p.degree()+1):
  c=p.nth(i)
  if not c:continue
  point=(i,v2(c))
  while len(hull)>1 and (hull[-1][0]-hull[-2][0])*(point[1]-hull[-1][1]) <= (hull[-1][1]-hull[-2][1])*(point[0]-hull[-1][0]):hull.pop()
  hull.append(point)
 return hull
records=[];identities=0
pairs=sorted(set([(k,n) for k in range(2,17) for n in range(1,10)]+[(k,k-1) for k in range(3,25)]+[(k,n) for k in range(17,29) for n in [1,2,3]]))
for k,n in pairs:
 p=V(k,n);A=2*t**(k-1)-t-1
 numerator=(t+1)*t**(n-1)*(2*t**n-t-1)*(t-1)**2+A*((t**(n-1)-1)*(2*t**n-t-1)+t*(t**n-1)*(t-1))
 assert s.Poly(numerator,t)==p*s.Poly((t-1)**3,t);identities+=1
 fac=s.factor_list(p.as_expr(),t)[1];degs=[s.degree(f,t) for f,e in fac for _ in range(e)]
 expected=k>=3 and n==k-1
 hull=polygon(p)
 if k>=5 and n>=4 and n!=k-1:
  d=2*n+k-5;d0=max(2*n-1,n+k-2)
  assert p.LC()==4 and hull==[(0,0),(d0,1),(d,2)]
 records.append(dict(k=k,n=n,degree=p.degree(),factor_degrees=[int(d) for d in degs],expected_reducible=expected,actual_reducible=len(degs)>1,newton_polygon=hull))
 if expected:
  f=s.Poly(1+2*sum(t**i for i in range(1,k-1)),t);g=V(2,k-2)+s.Poly(2*t**(k-2)*(1+t),t)
  assert f*g==p
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),pairs=len(records),exact_sparse_identity_checks=identities,disagreements=[r for r in records if r['actual_reducible']!=r['expected_reducible']],records=records,scope='Exact finite factorization and algebra controls only. No universal irreducibility proof.')
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print({k:v for k,v in out.items() if k!='records'})
