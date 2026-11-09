import itertools as it,json,pathlib
from fractions import Fraction as F
L=pathlib.Path(__file__).resolve().parent
def closure(n,edges):
 r=set(edges)
 for k in range(n):
  for i in range(n):
   for j in range(n):
    if (i,k) in r and (k,j) in r:r.add((i,j))
 return r
def extensions(n,r):return [p for p in it.permutations(range(n)) if all(p.index(a)<p.index(b) for a,b in r)]
def matrix(n,r,ps):
 idx={p:i for i,p in enumerate(ps)};A=[[F(0) for p in ps] for q in ps]
 for row,p in enumerate(ps):
  for i in range(n):
   for j in range(n):
    q=list(p)
    for k in (range(i,j) if i<j else range(i-1,j-1,-1)):
     a,b=q[k:k+2]
     if (a,b) not in r and (b,a) not in r:q[k],q[k+1]=b,a
    A[row][idx[tuple(q)]]+=F(1,n*n)
 return A
def energy(A,v):return sum(v[i]*A[i][j]*v[j] for i in range(len(v)) for j in range(len(v)))
def inertia(A):
 A=[r[:] for r in A];pos=neg=0
 while A:
  n=len(A);k=next((i for i in range(n) if A[i][i]),None)
  if k is None:
   edge=next(((i,j) for i in range(n) for j in range(i+1,n) if A[i][j]),None)
   if edge is None:return [pos,neg,n]
   i,j=edge
   # Congruence basis replacement e_i -> e_i+e_j produces nonzero diagonal.
   for t in range(n):A[i][t]+=A[j][t]
   for t in range(n):A[t][i]+=A[t][j]
   k=i
  if k:
   A[0],A[k]=A[k],A[0]
   for row in A:row[0],row[k]=row[k],row[0]
  d=A[0][0];pos+=d>0;neg+=d<0
  A=[[A[i][j]-A[i][0]*A[0][j]/d for j in range(1,n)] for i in range(1,n)]
 return [pos,neg,0]
result={'A_controls':0,'B_splits':0,'scope':'naturally labeled transitive orders n=2..4; bounded bridge tests only','A_obstruction':None,'B_obstruction':None}
for n in range(2,5):
 pairs=list(it.combinations(range(n),2))
 for mask in range(1<<len(pairs)):
  r={p for i,p in enumerate(pairs) if mask>>i&1}
  if closure(n,r)!=r:continue
  ps=extensions(n,r);m=len(ps)
  if m<2:continue
  M=matrix(n,r,ps)
  if result['A_obstruction'] is None:
   H=[[F(0) for p in ps] for q in ps]
   fiber_sizes=[]
   for x in range(n):
    fs={}
    for i,p in enumerate(ps):fs.setdefault(tuple(y for y in p if y!=x),[]).append(i)
    fiber_sizes.append([len(v) for v in fs.values()])
    for f in fs.values():
     for i in f:
      for j in f:H[i][j]+=F(1,n*len(f))
   D=[[H[i][j]-M[i][j] for j in range(m)] for i in range(m)]
   result['A_controls']+=1
   if inertia(D)[1]:
    for v in it.product([-1,0,1],repeat=m):
     if energy(D,v)<0:
      result['A_obstruction']=dict(n=n,relations=sorted(r),extensions=ps,vector=v,raw_quadratic=str(energy(D,v)),uniform_energy_difference=str(energy(D,v)/m),M=M,H=H,fiber_sizes=fiber_sizes);break
  if result['B_obstruction'] is None:
   for a,b in pairs:
    if (a,b) in r:continue
    plus=closure(n,r|{(a,b)});minus=closure(n,r|{(b,a)})
    Mp=matrix(n,plus,extensions(n,plus));Mm=matrix(n,minus,extensions(n,minus));ip={p:i for i,p in enumerate(extensions(n,plus))};im={p:i for i,p in enumerate(extensions(n,minus))}
    S=[[Mp[ip[p]][ip[q]] if p in ip and q in ip else Mm[im[p]][im[q]] if p in im and q in im else F(0) for q in ps] for p in ps]
    D=[[S[i][j]-M[i][j] for j in range(m)] for i in range(m)];ine=inertia(D);result['B_splits']+=1
    if ine[0]>1:
     result['B_obstruction']=dict(n=n,relations=sorted(r),split=(a,b),extensions=ps,inertia=ine,difference=D);break
  if result['A_obstruction'] and result['B_obstruction']:break
 if result['A_obstruction'] and result['B_obstruction']:break
(L/'exact-capped-checks.json').write_text(json.dumps(result,default=str,indent=2));print(json.dumps(result,default=str))
