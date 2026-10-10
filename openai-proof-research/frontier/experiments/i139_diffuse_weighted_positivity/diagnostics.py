"""New finite checks only. No universal proof or contribution certification."""
from fractions import Fraction as F
from itertools import product
from math import comb

def mons(n,m):return [u for u in product(range(m+1),repeat=n) if sum(u)<=m]
def rank(A,p):
 A=[row[:] for row in A];r=0
 for c in range(len(A[0])):
  q=next((q for q in range(r,len(A)) if A[q][c]%p),None)
  if q is None:continue
  A[r],A[q]=A[q],A[r];z=pow(A[r][c]%p,-1,p);A[r]=[v*z%p for v in A[r]]
  for i in range(len(A)):
   if i!=r:
    z=A[i][c]%p;A[i]=[(v-z*w)%p for v,w in zip(A[i],A[r])]
  r+=1
  if r==len(A):break
 return r

def run():
 cases=[];p=1009
 for n in [2,3]:
  for m1,m2 in [(0,2),(1,3),(2,1),(3,2)]:
   A=mons(n,m1);B=[(u[0]+m1+3,)+u[1:] for u in mons(n,m2)];cols=A+B;rows=[(j,u) for j,m in enumerate([m1,m2]) for u in mons(n,m)]
   cut=m1+1;lim=[];numeric=[];exps=[]
   for j,alpha in rows:
    lr=[];nr=[];er=[]
    for u in cols:
     v=1
     for ui,ai in zip(u,alpha):v*=comb(ui,ai) if ui>=ai else 0
     e=max(0,u[0]-cut)-(u[0]-cut if j else 0);assert e>=0
     lr.append(v%p if e==0 else 0);nr.append(v*pow(2,e,p)%p);er.append(e)
    lim.append(lr);numeric.append(nr);exps.append(er)
   assert rank(lim,p)==len(rows)
   # A particular nonzero parameter is a finite independent rank check.
   rr=rank(numeric,p);assert rr==len(rows)
   cases.append(dict(dimension=n,orders=[m1,m2],rows=len(rows),limit_rank=len(rows),parameter=2,modulus=p,rank=rr))
 cells=0
 for n in [3,4,5]:
  for D in [1,2,3]:
   for V in [1,2,7]:
    a=F(1,D);b=F(D**(n-1)*V);T=b/a;assert T.denominator==1
    for t in [F(1,9),F(1,3),F(1,2),F(8,9)]:
     # Columns ei-T en and -en have determinant -1 by triangularity.
     for i in range(n-1):
      out=[F(0)]*n;out[i]=a;out[-1]=b-T*a;assert out[-1]==0
     assert b-(1-t)*b==t*b
     assert a**(n-1)*(t*b)+a**(n-1)*((1-t)*b)==V
     cells+=1
 trees=0
 for N in range(8,257,8):
  R=F(9*N,8);root=1/R;small=root/8
  assert N*root+N*small==1 and root==F(8,9*N) and small==F(1,9*N)
  trees+=1
 obstruct=0
 for N in range(1,256,2):
  hi=F(2,3*N);lo=F(1,3*N)
  assert N*(hi+lo)==1 and (1/hi).denominator==2
  obstruct+=1
 for n in range(3,7):
  for w in [F(1,2),F(1,3),F(1,10)]:
   assert w**n<w # axis a=1, exact-capacity last intercept
 assert F(99,100)**3*81>64 and F(99,100)**3*F(4,3)>1
 return dict(status='PASS',coherent_block_examples=cases,two_cell_identities=cells,exact_eight_branch_forests=trees,reciprocal_obstructions=obstruct,scope='Finite instances only; not universal proof, contribution, human review or priority certification')
if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2))
