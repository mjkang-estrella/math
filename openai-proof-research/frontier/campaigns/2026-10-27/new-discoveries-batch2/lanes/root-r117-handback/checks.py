import itertools,json,random
from pathlib import Path
L=Path(__file__).resolve().parent
def mm(A,B):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*B)] for row in A]
def identity(n):return [[int(i==j) for j in range(n)] for i in range(n)]
def perm(A,I):
 I=list(I)
 return sum(__import__('math').prod(A[i][j] for i,j in zip(I,p)) for p in itertools.permutations(I))
def dp(A,I):
 I=list(I);D={0:1}
 for i in I:
  E={}
  for mask,v in D.items():
   for j,k in enumerate(I):
    if not mask>>j&1:E[mask|1<<j]=E.get(mask|1<<j,0)+v*A[i][k]
  D=E
 return D.get((1<<len(I))-1,1)
def defect(A,h,fn=perm):
 n=len(A)
 return fn(A,range(h))*fn(A,range(h,n))-fn(A,range(0,n,2))*fn(A,range(1,n,2))
random.seed(117);tests=[]
for n in range(2,9):
 for t in range(8):
  A=identity(n)
  for z in range(4*n):
   E=identity(n);i=random.randrange(n-1);a=random.randrange(4)
   if random.randrange(2):E[i][i+1]=a
   else:E[i+1][i]=a
   A=mm(A,E)
  for h in range(1,n):
   # Pad the smaller end; balanced cut retains the original cut.
   d=abs(n-2*h);N=n+d;B=identity(N);off=d if 2*h<n else 0
   for i in range(n):
    for j in range(n):B[off+i][off+j]=A[i][j]
   lhs=defect(A,h);ind=defect(A,h,dp);padded=defect(B,N//2,dp)
   assert lhs==ind==padded
   assert lhs>=0
   tests.append({'n':n,'h':h,'trial':t,'defect':lhs,'padding':d})
# A deliberately non-TNN matrix defeats the inequality: tests do not forget the domain.
A=[[1,0,1],[0,1,0],[1,0,1]]
assert defect(A,1)==-1
r={'status':'PASS','exact_padding_checks':len(tests),'independent_methods':'permutation expansion versus subset DP','negative_control':{'matrix':A,'defect':-1,'minor_rows':[0,1],'minor_cols':[1,2],'minor':-1},'tests':tests,'limit':'finite diagnostics only; universal padding argument is in route.md'}
(L/'check-results.json').write_text(json.dumps(r,indent=2));print({k:v for k,v in r.items() if k!='tests'})
