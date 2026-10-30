import math,json
from pathlib import Path
L=Path(__file__).resolve().parent
def add(z,w):return(z[0]+w[0],z[1]+w[1])
def neg(z):return(-z[0],-z[1])
def mul(z,w):return(z[0]*w[0]-z[1]*w[1],z[0]*w[1]+z[1]*w[0])
def power(z,k):
 r=(1,0)
 while k:
  if k&1:r=mul(r,z)
  z=mul(z,z);k//=2
 return r
def root(z):
 a,b=z;N=a*a+b*b;s=math.isqrt(N)
 if s*s!=N:return None
 if (s+a)%2:return None
 u=math.isqrt((s+a)//2)
 if u*u!=(s+a)//2:return None
 if u:
  if b%(2*u):return None
  v=b//(2*u)
 else:
  if b:return None
  v=math.isqrt(-a)
 r=(u,v)
 return r if mul(r,r)==z else None
def f2red(c):
 if root(c)!=None:return True
 t=root(add((-1,0),neg(c)))
 return t!=None and any(root(add((0,1),s))!=None for s in [t,neg(t)])
records=[];violations=[];squares=[];eligible=0;comparisons=0
for a in range(-40,41):
 for b in range(-40,41):
  c=(a,b)
  if c in [(0,0),(-1,0)]:continue
  red=f2red(c);eligible+=not red;A=(1,0)
  for n in range(2,9):
   v=add(mul(A,A),power(c,2**(n-1)-1))
   if n>=3:
    comparisons+=1;s=root(v)
    if s is not None:
     bs=[mul((0,1),add(A,t)) for t in [s,neg(s)]]
     rec=dict(c=c,n=n,a=v,s=s,b=bs,b_square=[root(x)!=None for x in bs],f2_reducible=red)
     squares.append(rec)
     if not red and any(rec['b_square']):violations.append(rec)
   A=v
# Exact independently known public witness and source exceptional parameter.
for c,s in [((0,-2),(1,2)),((-89,0),(0,835))]:
 A=add(c,(1,0));v=add(power(c,3),mul(A,A));assert mul(s,s)==v
 bs=[mul((0,1),add(A,t)) for t in [s,neg(s)]]
 records.append(dict(c=c,a3=v,b=bs,b_roots=[root(x) for x in bs],f2_reducible=f2red(c)))
assert records[0]['b_roots']==[(1,1),(2,0)]
assert records[0]['f2_reducible'] and not records[1]['f2_reducible']
assert not violations
# Fixed congruence obstruction controls, not global irreducibility checks.
local=[]
for M in [2,3,4,5,7,8,11,16,105,2310]:
 c=(-3*M*M,0);assert not f2red(c)
 A=(1,0)
 for n in range(2,9):
  A=add(mul(A,A),power(c,2**(n-1)-1));assert A[0]%M==1%M and A[1]%M==0
 local.append(dict(M=M,c=c))
out=dict(scope='finite diagnostic only; no universal stability proof',box=40,max_n=8,eligible_parameters=eligible,comparisons=comparisons,a_n_square_records=squares,violations=violations,controls=records,local_controls=local)
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print('eligible',eligible,'comparisons',comparisons,'square records',len(squares),'violations',len(violations))
