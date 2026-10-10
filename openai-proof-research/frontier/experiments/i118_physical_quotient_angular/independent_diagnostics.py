"""Independent finite algebra; no imports of inherited matrix constructors."""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction as Q
from pathlib import Path
import json, math
ROOT=Path(__file__).resolve().parents[3]
def mon(r):return [(i,j,r-i-j) for i in range(r+1) for j in range(r-i+1)]
def derivative(m,a):
 n=list(m)
 if not n[a]:return None,0
 c=n[a];n[a]-=1
 return tuple(n),c
def matrix(r):
 # Build each column by applying the operator to one polynomial basis vector.
 lo=mon(r-1);hi=mon(r)
 eq=[(q,a,b,m) for q in range(3) for a in range(3) for b in range(a,3) for m in lo]+[('trace',m) for m in hi]
 ix={k:i for i,k in enumerate(eq)};cols=[]
 for v in range(3):
  for q in range(3):
   for m in hi:
    c=[0]*len(eq)
    for a in range(3):
     for b in range(a,3):
      if b==v:
       n,z=derivative(m,a)
       if z:c[ix[q,a,b,n]]+=3*z
      if a==v:
       n,z=derivative(m,b)
       if z:c[ix[q,a,b,n]]+=3*z
      if a==b:
       n,z=derivative(m,v)
       if z:c[ix[q,a,b,n]]-=2*z
    if v==q:c[ix['trace',m]]=1
    cols.append(c)
 for v in range(3):
  for m in lo:
   c=[0]*len(eq)
   for q in range(3):
    for a in range(3):
     for b in range(a,3):c[ix[q,a,b,m]]= -3*(a==q)*(b==v)-3*(b==q)*(a==v)+2*(a==b)*(q==v)
   cols.append(c)
 return [list(x) for x in zip(*cols)]
def determinant(a,p):
 a=[x[:] for x in a];d=1;n=len(a)
 for j in range(n):
  k=next((k for k in range(j,n) if a[k][j]%p),None)
  if k is None:return 0
  if k!=j:a[k],a[j]=a[j],a[k];d=-d
  v=a[j][j]%p;d=d*v%p;iv=pow(v,-1,p)
  for k in range(j+1,n):
   z=a[k][j]*iv%p
   if z:
    for l in range(j,n):a[k][l]=(a[k][l]-z*a[j][l])%p
 return d%p

def check():
 cert=json.loads((ROOT/'frontier/experiments/i115_physical_elasticity_continuation/diagnostic-result.json').read_text())['certificate']
 p=cert['prime'];assert all(p%d for d in range(2,math.isqrt(p)+1))
 a=matrix(4);assert (len(a),len(a[0]))==(195,165)
 det=determinant([a[i] for i in cert['row_indices']],p);assert det==166021
 # Exact homogeneous formulas, at arbitrary tested rational admissible constants.
 tests=0
 for m,k in [(Q(1),Q(1)),(Q(2),Q(1)),(Q(1),Q(4)),(Q(3,2),Q(2,3))]:
  assert k>m/3
  for l in range(31):
   den=Q(2)*(2*l+3)*(l+1)
   aa=((4*l+2)+2*l*k/m)/den
   bb=(-(k/m)*(l+3)-2)/den
   assert aa*(l+3)+2*l*bb==1
   assert 2*aa+(4*l+2)*bb==-k/m
   assert aa>0
   tests+=1
  for d in range(2,32):
   c=-k/(m*(4*d-2)+2*k*(d-1))
   assert m*c*(4*d-2)+k*(1+2*c*(d-1))==0
   tests+=1
  b=15*k/(2*(3*m+k));aa=1-b/3
  assert aa+b/3==1
  assert b*Q(2,15)==k/(3*m+k)
 return dict(status='PASS finite exact algebra only',degree_four_minor=dict(rows=195,columns=165,prime=p,determinant=det),homogeneous_identity_instances=tests,scope='Independent finite certificate and rational instances; universal statements rest on displayed proofs; no A* or P112 certification')
if __name__=='__main__':print(json.dumps(check(),indent=2))
