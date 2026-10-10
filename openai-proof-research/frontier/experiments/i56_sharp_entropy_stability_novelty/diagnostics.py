"""Read-only exact rational checks for I56; finite checks are not universal proofs."""
from fractions import Fraction as F
from itertools import combinations_with_replacement,permutations,product
import json,random
checks=0

def check(c):
 global checks
 checks+=1
 assert c

def tensor(m,values):
 t={}
 for key,v in values.items():
  for p in set(permutations(key)):t[p]=v
 return t

def derivative(m,t):
 out={}
 for a,b in product(range(m),repeat=2):
  v=t.get((a,b,b),0)+t.get((a,b,a),0)
  if v:out[(0,a,b)]=v
 for r,s,a,b in product(range(m),repeat=4):
  v=((a==r)-(b==r))*t.get((a,b,s),0)+((b==s)-(a==s))*t.get((a,b,r),0)
  if v:out[(1,r,s,a,b)]=v
 return out

def normal(m,t):
 vals={}
 for i,j,k in combinations_with_replacement(range(m),3):
  if i==j==k or len({i,j,k})==3:vals[i,j,k]=t.get((i,j,k),0)
  else:
   a,b=min(i,j,k),max(i,j,k)
   vals[i,j,k]=F(t.get((a,a,b),0)+t.get((a,b,b),0),2)
 return tensor(m,vals)

def dot(a,b):return sum(v*b.get(k,0) for k,v in a.items())
def add(a,b):return {k:a.get(k,0)+b.get(k,0) for k in a.keys()|b.keys()}
def scaled(a,c):return {k:v*c for k,v in a.items()}

def residual(m,t,subtract=True):
 out={}
 for a,b in product(range(m),repeat=2):
  out[(0,a,b)]=sum(t.get((a,k,r),0)*t.get((k,b,r),0) for r,k in product(range(m),repeat=2))-int(subtract and a==b)
 for r,s,a,b in product(range(m),repeat=4):
  out[(1,r,s,a,b)]=sum(t.get((a,k,r),0)*t.get((k,b,s),0)-t.get((a,k,s),0)*t.get((k,b,r),0) for k in range(m))
 return out

rows=[]
for m in range(1,8):
 keys=list(combinations_with_replacement(range(m),3));bs=[tensor(m,{k:1}) for k in keys];ds=[derivative(m,t) for t in bs];ns=[normal(m,t) for t in bs]
 # All Gram entries prove the displayed identity on each finite-dimensional test space.
 for i in range(len(bs)):
  for j in range(i,len(bs)):check(dot(ds[i],ds[j])==4*dot(ns[i],ns[j]))
 for i,j in combinations_with_replacement(range(m),2):
  if i==j:continue
  v=tensor(m,{(i,i,j):1,(i,j,j):-1});check(not derivative(m,v));check(dot(normal(m,v),normal(m,v))==0)
 rows.append({'m':m,'symmetric_dimension':len(bs),'kernel_dimension':m*(m-1)//2,'normal_dimension':len(bs)-m*(m-1)//2,'normal_squared_singular_value':4})

rng=random.Random(56053)
for m in range(1,5):
 D=tensor(m,{(i,i,i):1 for i in range(m)})
 for trial in range(8):
  E=tensor(m,{k:F(rng.randint(-4,4),100*m*m) for k in combinations_with_replacement(range(m),3)})
  Q=residual(m,E,False);DR=derivative(m,E);R=residual(m,add(D,E))
  for k in R:check(R[k]==DR.get(k,0)+Q.get(k,0))
  n2=dot(E,E);check(dot(Q,Q)<=5*n2*n2)
  N=normal(m,E);RN=residual(m,add(D,N)); nn2=dot(N,N)
  # sqrt(5)||N|| <= 1 and ||R(D+N)|| >= ||N|| (normal-chart bound).
  check(5*nn2<=1);check(dot(RN,RN)>=nn2)
# Omitting normalization has radial kernel; triple symmetry is indispensable.
for m in range(1,7):
 t=tensor(m,{(0,0,0):1});dr=derivative(m,t)
 check(all(v==0 for k,v in dr.items() if k[0]==1));check(dr[(0,0,0)]==2)
# Exact rational orthogonal rotation of a normalized tensor; residual and derivative norm equivariance.
m=2; U=[[F(3,5),F(-4,5)],[F(4,5),F(3,5)]]
def rotate(t):
 return {(i,j,k):sum(U[i][a]*U[j][b]*U[k][c]*t.get((a,b,c),0) for a,b,c in product(range(m),repeat=3)) for i,j,k in product(range(m),repeat=3)}
D=tensor(m,{(0,0,0):1,(1,1,1):1});E=tensor(m,{(0,0,0):F(1,100),(0,0,1):F(2,100),(0,1,1):F(-3,100),(1,1,1):F(4,100)})
check(dot(residual(m,rotate(D)),residual(m,rotate(D)))==0)
check(dot(residual(m,rotate(add(D,E))),residual(m,rotate(add(D,E))))==dot(residual(m,add(D,E)),residual(m,add(D,E))))
check(dot(rotate(E),rotate(E))==dot(E,E))
print(json.dumps({'status':'PASS','assertions':checks,'exact_gram_spaces':rows,'checks':['full derivative Gram matrices','orbit tangent kernel','exact quadratic Taylor remainder','quadratic remainder bound','normal-chart residual lower bound','normalization necessity','rational orthogonal equivariance'],'scope':'Finite exact identities; universal proof and compactness argument are written in the review.'},indent=2,sort_keys=True))
