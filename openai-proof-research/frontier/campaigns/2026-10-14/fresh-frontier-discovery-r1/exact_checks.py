#!/usr/bin/env python3
"""Exact finite support checks. No entropy-rigidity theorem is certified."""
from fractions import Fraction as Q
from collections import defaultdict
from pathlib import Path
import json,math

def add(a,b):
 c=defaultdict(Q,a)
 for I,x in b.items():c[I]+=x
 return {I:x for I,x in c.items() if x}
def scale(a,s):return {I:x*s for I,x in a.items() if x*s}
def wedge(a,b):
 c=defaultdict(Q)
 for I,x in a.items():
  for J,y in b.items():
   if set(I)&set(J):continue
   inv=sum(i>j for i in I for j in J)
   c[tuple(sorted(I+J))]+=x*y*(-1 if inv%2 else 1)
 return {I:x for I,x in c.items() if x}
def power(a,k):
 ans={():Q(1)}
 for _ in range(k):ans=wedge(ans,a)
 return ans
def contract(a,v):
 c=defaultdict(Q)
 for I,x in a.items():
  for k,i in enumerate(I):
   if v.get(i,0):c[I[:k]+I[k+1:]]+=x*v[i]*(-1 if k%2 else 1)
 return {I:x for I,x in c.items() if x}
rows=[]
for n in range(2,8):
 alpha={(0,):Q(1)}
 omega={}
 for j in range(1,n):omega=add(omega,wedge({(n+j-1,):Q(1)},{(j,):Q(1)}))
 for seed in range(1,6):
  bs=[Q((i+1)*seed-3,11+seed) for i in range(n)]
  beta={(i,):x for i,x in enumerate(bs) if x}
  B={(i,j):Q((2*i-j+seed)%7-3,7+seed) for i in range(n) for j in range(i+1,n)}
  B={I:x for I,x in B.items() if x}
  actual=wedge(add(alpha,beta),power(add(omega,B),n-1))
  expected=scale(wedge(alpha,power(omega,n-1)),1+bs[0])
  assert actual==expected
  flip_alpha=add(scale(alpha,-1),beta)
  flip_omega=add(scale(omega,-1),B)
  assert add(flip_alpha,add(alpha,beta))==scale(beta,2)
  assert add(flip_omega,add(omega,B))==scale(B,2)
  # At v=e_1, X=d/dq_1 and the magnetic vertical correction is -B_1j.
  Z={0:Q(1)}
  for j in range(1,n):Z[n+j-1]=-B.get((0,j),0)
  assert not contract(add(omega,B),Z)
  assert contract(add(alpha,beta),Z)=={():1+bs[0]}
  rows.append({'n':n,'fixture':seed,'volume_identity':True,
               'flip_defect':True,'reeb_kernel_and_normalization':True})
spectra=[]
for m in range(2,12):
 exps=[2]+[1]*(2*m-2)
 gap=len(exps)*sum(x*x for x in exps)-sum(exps)**2
 assert gap==2*m-2>0
 spectra.append({'complex_dimension':m,'unstable_multiplicities':{'2':1,'1':2*m-2},
                 'scalar_cauchy_schwarz_gap':gap})
# Elementary symplectic hyperbolic data admit a pure-stable coisotropic plane.
planes=[]
for m in range(1,9):
 J=[[0]*(2*m) for _ in range(2*m)]
 for i in range(m):J[i][m+i]=1;J[m+i][i]=-1
 D=[-1]*m+[1]*m
 assert all(J[i][j]==0 for i in range(m) for j in range(m))
 assert all(J[i][m+j]==int(i==j) for i in range(m) for j in range(m))
 assert all((D[i]+D[j])*J[i][j]==0 for i in range(2*m) for j in range(2*m))
 planes.append({'stable_dimension':m,'L_equals_P_equals_Estable':True,
                'L_coisotropic':True,'P_unstable_rank':0,
                'scope':'not a model of all source formal-Lie-algebra hypotheses'})
out={'status':'support only; full Randers entropy rigidity remains unresolved',
     'arithmetic':'Python Fraction / integers; no floats or random simulations',
     'contact_form_fixtures':rows,'rank_one_trace_checks':spectra,'one_sided_plane_checks':planes}
Path(__file__).with_name('exact-results.json').write_text(json.dumps(out,indent=2)+'\n')
print('Passed: 30 exact contact-form fixtures, 10 trace-spectrum checks, 8 elementary symplectic examples.')
