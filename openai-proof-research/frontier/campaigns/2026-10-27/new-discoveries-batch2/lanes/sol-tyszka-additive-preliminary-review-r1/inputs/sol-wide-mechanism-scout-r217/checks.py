from fractions import Fraction as F
from itertools import product,combinations
import json,random
import numpy as np
from scipy.optimize import linprog
import sympy as s
random.seed(217)
def forms(n):
 out=[(tuple(int(j==i) for j in range(n)),F(-1)) for i in range(n)]
 out+= [(tuple(int(h==i)+int(h==j)-int(h==k) for h in range(n)),F(0)) for i in range(n) for j in range(i,n) for k in range(n)]
 return sorted(set(out))
def ev(a,c,x):return sum(v*w for v,w in zip(a,x))+c
tested=0
for n in range(1,7):
 for trial in range(12):
  x=[F(random.randint(-300,300),random.randint(1,13)) for _ in range(n)]
  fs=forms(n);A=[];b=[]
  for a,c in fs:
   r=ev(a,c,x)
   for sign in [-1,1]:A.append([sign*v for v in a]);b.append(abs(r)-sign*c)
  res=linprog([random.random() for _ in range(n)],A_ub=np.array(A,dtype=float),b_ub=np.array(b,dtype=float),bounds=[(-2**(n-1),2**(n-1))]*n,method='highs',options={'threads':1,'parallel':False})
  assert res.success,res.message
  # Floating point chooses a vertex; independent rational arithmetic certifies it.
  y=[F(float(t)).limit_denominator(10**8) for t in res.x]
  assert all(abs(t)<=2**(n-1) for t in y)
  assert all(abs(ev(a,c,y))<=abs(ev(a,c,x)) for a,c in fs),(n,x,y)
  tested+=1
minors=0;vertex_count=0
for n in range(1,4):
 fs=forms(n)
 for eq in combinations(fs,n):
  A=s.Matrix([a for a,c in eq]);d=A.det()
  if not d:continue
  z=A.inv()*s.Matrix([-c for a,c in eq]);assert max(abs(t) for t in z)<=2**(n-1);vertex_count+=1
 # all minors of two additive rows at n=3, one row at n=2
 if n>1:
  rows=sorted({a for a,c in fs if c==0})
  for rr in product(rows,repeat=n-1):
   for col in range(n):
    M=s.Matrix([[a[j] for j in range(n) if j!=col] for a in rr]);assert abs(M.det())<=2**(n-1);minors+=1
out={'seed':217,'exact_residual_certificates':tested,'all_arrangement_bases_n_le_3':vertex_count,'additive_cofactor_controls':minors,'limits':'finite arithmetic controls; floating point only selects certificates; exact Fraction/Sympy assertions verify; no proof/novelty inferred'}
print(json.dumps(out,indent=2))
