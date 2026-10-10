"""Finite rational diagnostics only; analytic proofs and limits are in the report."""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction as F
from itertools import product
import json

def check():
 variance=0
 for n in range(2,9):
  weights=[F(j,n*(n+1)//2) for j in range(1,n+1)]
  for shift in range(5):
   vals=[(F((j+shift)**2-3*j),F(j*j*j-shift)) for j in range(n)]
   sq=lambda z:z[0]**2+z[1]**2
   mean=tuple(sum(w*v[k] for w,v in zip(weights,vals)) for k in range(2))
   lhs=sum(w*sq(v) for w,v in zip(weights,vals))
   diff=sum(weights[i]*weights[j]*sq(tuple(vals[i][k]-vals[j][k] for k in range(2))) for i in range(n) for j in range(n))/2
   assert lhs==sq(mean)+diff;variance+=1
 # Incidence second moment = integral of pair multiplicities, tested on actual rational tubes.
 tube_rows=[]
 pts=list(product([F(i,4) for i in range(5)],repeat=2))
 weights=[F(i+1,len(pts)*(len(pts)+1)//2) for i in range(len(pts))]
 for M in (4,8,16):
  theta=F(1,M);catalog=[]
  for k in range(-M,M+1):
   slope=F(k,M)
   for j in range(-2*M,2*M+1):
    members={i for i,(x,y) in enumerate(pts) if abs(y-slope*x-F(j,M))<=theta}
    if members:catalog.append(members)
  masses=[sum(weights[i] for i in t) for t in catalog]
  lhs=sum(m*m for m in masses)
  rhs=F(0);max_count=0
  for i,p in enumerate(pts):
   for j,q in enumerate(pts):
    count=sum(i in t and j in t for t in catalog);max_count=max(max_count,count)
    rhs+=weights[i]*weights[j]*count
    assert count<=16*M
    if i!=j:assert count*count*sum((p[k]-q[k])**2 for k in range(2))<=256
  assert lhs==rhs
  for B in (2,4,8):
   selected=[m for m in masses if m>B*theta]
   assert sum(selected)**2<=len(selected)*sum(m*m for m in selected)
  tube_rows.append(dict(M=M,tubes=len(catalog),points=len(pts),second_moment=str(lhs),max_pair_multiplicity=max_count))
 schedules=[]
 for s in (F(5,4),F(4,3),F(3,2),F(7,4)):
  prev=0;m=0;rows=[]
  for j in range(1,7):
   b=max(20,(j+4)*10*prev);mb=m+2*(b-prev);a=mb*s.denominator//s.numerator;L=a-b
   assert mb>=s*b and mb>=s*a and 0<=mb-s*a<s and L>0
   assert F(mb,b)<=2 and F(mb,a)>=s
   # Exact exponent identity, with rounding error at most one half.
   assert abs(F(L,2)-((F(mb,b)/s-1)*b/2))<F(1,2)
   rows.append(dict(free_end=b,frozen_end=a,mass_log2=mb,freeze_length=L,energy_growth_log2_lower_without_constant=str(F(L,2))))
   prev=a;m=mb
  schedules.append(dict(s=str(s),stages=rows))
 return dict(status='PASS finite exact instances only',variance_instances=variance,tube_instances=tube_rows,moran_schedules=schedules,scope='Finite variance, actual rational tube multiplicity/second-moment and branching arithmetic; no universal analytic or substantiality certification')
if __name__=='__main__':print(json.dumps(check(),indent=2))
