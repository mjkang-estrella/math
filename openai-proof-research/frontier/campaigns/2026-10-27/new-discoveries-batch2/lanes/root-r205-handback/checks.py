from itertools import combinations
from math import factorial,comb
from fractions import Fraction
import json

def exps(n,d):
 if n==1:return [(d,)]
 return [(i,)+e for i in range(d+1) for e in exps(n-1,d-i)]
def product(forms):
 n=len(forms[0]);f={(0,)*n:1}
 for a in forms:
  g={}
  for e,c in f.items():
   for j,v in enumerate(a):
    t=list(e);t[j]+=1;t=tuple(t);g[t]=g.get(t,0)+c*v
  f={e:c for e,c in g.items() if c}
 return f
def cat(f,n,d,k):
 rows=exps(n,d-k);cols=exps(n,k)
 return [[f.get(tuple(a+b for a,b in zip(r,c)),0)*factorial_product(tuple(a+b for a,b in zip(r,c)))//factorial_product(r) for c in cols] for r in rows]
def factorial_product(e):
 z=1
 for a in e:z*=factorial(a)
 return z
def rank(A,p=None):
 A=[[x%p if p else Fraction(x) for x in r] for r in A];r=0
 for j in range(len(A[0])):
  i=next((i for i in range(r,len(A)) if A[i][j]),None)
  if i is None:continue
  A[r],A[i]=A[i],A[r];v=pow(A[r][j],-1,p) if p else 1/A[r][j]
  A[r]=[(x*v)%p if p else x*v for x in A[r]]
  for i in range(r+1,len(A)):
   v=A[i][j]
   if v:A[i]=[(a-v*b)%p if p else a-v*b for a,b in zip(A[i],A[r])]
  r+=1
  if r==len(A):break
 return r
out=[]
for n in range(2,6):
 for d in range(2*n,2*n+(5 if n<5 else 2)):
  forms=[[t**j for j in range(n)] for t in range(1,d+1)];f=product(forms);k=d//2;A=cat(f,n,d,k);r=rank(A,1009)
  out.append(dict(n=n,d=d,k=k,prime=1009,rows=len(A),columns=len(A[0]),rank=r,full=r==len(A[0])))
# Known source counterexamples: actual rational ranks, not floating point.
harmonic={(3,1):1,(1,3):-1};h=cat(harmonic,2,4,2)
hessian={(4,1,1):1,(1,4,1):1,(1,1,4):1,(2,2,2):-3};q=cat(hessian,3,6,3)
assert rank(h)==2 and rank(q)==6
# The six algebraic factors reduce modulo 1009 via a primitive cube root.
p=1009;w=next(x for x in range(2,p) if (x*x+x+1)%p==0)
forms=[[1,0,0],[0,1,0],[0,0,1],[1,1,1],[1,w,w*w%p],[1,w*w%p,w]]
minor_ranks=[rank([forms[i] for i in ids],p) for ids in combinations(range(6),3)]
assert all(r==3 for r in minor_ranks)
method_controls=[]
for n,d in [(4,8),(5,10)]:
 f=product([[t**j for j in range(n)] for t in range(1,d+1)])
 A=cat(f,n,d,d//2)
 ranks={str(p):rank(A,p) for p in [1013,1019]}
 if n==4:ranks['Q']=rank(A)
 # A fixed integer perturbation, not a random repeat-until-pass search.
 forms=[[((t+2)**(j+1)+3*j*t*t+7*j*j)%37-18 for j in range(n)] for t in range(1,d+1)]
 r=rank(cat(product(forms),n,d,d//2),1009)
 method_controls.append(dict(n=n,d=d,momentcurve_ranks=ranks,perturbed_coefficients=forms,perturbed_rank_mod1009=r))
print(json.dumps(dict(method_controls=method_controls,scope='17 prescribed moment-curve arrangements over F_1009; rational-source counterexample ranks; no universal proof',cases=out,harmonic_rank=2,hessian_rank=6,nonzero_algebraic_maximal_minors=len(minor_ranks),omega=w),indent=2))
