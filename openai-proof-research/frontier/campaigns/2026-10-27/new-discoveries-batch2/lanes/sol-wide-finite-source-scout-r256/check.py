"""Bounded diagnostics, never the universal proof. Run ONLY through helper_guard.py."""
from itertools import product
from fractions import Fraction
from pathlib import Path
import json
L=Path(__file__).resolve().parent
def test(ns,m,cs):
 A=list(product(*[range(n) for n in ns]));els=[(a,b) for a in A for b in range(m)];N=len(els);index={x:i for i,x in enumerate(els)};zero=index[(tuple(0 for n in ns),0)]
 def f(a,b):return sum(a[i]*b[j]*c for (i,j),c in cs.items())%m
 for (i,j),c in cs.items():assert ns[i]*c%m==ns[j]*c%m==0
 add=[[index[(tuple((x+y)%n for x,y,n in zip(a,c,ns)),(b+d)%m)] for c,d in els] for a,b in els]
 mul=[[index[(tuple(0 for n in ns),f(a,c))] for c,d in els] for a,b in els]
 for i,j,k in product(range(N),repeat=3):
  assert mul[mul[i][j]][k]==mul[i][mul[j][k]]==zero
  assert mul[i][add[j][k]]==add[mul[i][j]][mul[i][k]]
  assert mul[add[i][j]][k]==add[mul[i][k]][mul[j][k]]
 for i,(a,b) in enumerate(els):
  for j,(c,d) in enumerate(els):assert (mul[i][j]==mul[j][i])==((f(a,c)-f(c,a))%m==0)
 count=sum(mul[i][j]==mul[j][i] for i,j in product(range(N),repeat=2))
 return dict(cyclic_orders=ns,target_order=m,coefficients={str(k):v for k,v in cs.items()},size=N,triples=N**3,cp=str(Fraction(count,N*N)))
rows=[test((2,2),2,{(0,1):1}),test((2,4),4,{(0,1):2}),test((4,4),4,{(0,1):1}),test((2,2,2),2,{(0,1):1,(0,2):1,(1,2):1})]
def group_cp(q,quaternion=False):
 els=list(product(range(q),range(q),range(q)))
 def mul(a,b):
  x,y,z=a;u,v,w=b
  return ((x+u)%q,(y+v)%q,(z+w+x*v+(x*u+y*v if quaternion else 0))%q)
 count=sum(mul(a,b)==mul(b,a) for a,b in product(els,repeat=2))
 return str(Fraction(count,len(els)**2))
assert group_cp(2)==group_cp(2,True)==rows[0]['cp']=='5/8'
assert group_cp(4)==rows[2]['cp']
out=dict(status='PASS',rings=rows,groups={'UT3_F2':group_cp(2),'Q8':group_cp(2,True),'UT3_Z4':group_cp(4)},failed_half_bracket={'A':'C2 x C2','B':'C2','bracket_nonzero':True,'antisymmetric_product_is_commutative':True},scope='finite diagnostics only')
(L/'checks.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
