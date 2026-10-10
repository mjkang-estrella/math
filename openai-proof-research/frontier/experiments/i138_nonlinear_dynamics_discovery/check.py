"""Finite exact diagnostics; no simulation or universal theorem certification."""
from fractions import Fraction as F
from itertools import product

def run():
 counts={}
 n=0
 for M,a,b,u in product([F(1,2),F(1),F(3)], [F(0),F(1,3),F(2)], [F(0),F(2,3),F(2)], [F(1,5),F(1,2),F(4,5)]):
  B=M*u; A=M-B; Bp=a*A*B-b*B*B; Ap=-Bp;r=A/B
  assert (Ap*B-A*Bp)/(B*B)==-M*a*r+M*b
  assert Ap+Bp==0
  n+=1
 counts['physical_ratio_and_conservation']=n
 n=0
 # Positive stochastic matrices: independent direct l1 computation and
 # common-column subtraction, including different initial distributions.
 for size in range(2,6):
  for denominator in range(2*size,2*size+5):
   b=F(1,denominator);theta=1-size*b
   for shift in range(size):
    U=[[b+theta*int(i==(j+shift)%size) for j in range(size)] for i in range(size)]
    for j,k in product(range(size),repeat=2):
     v=[F(int(i==j)-int(i==k)) for i in range(size)]
     w=[sum(U[i][l]*v[l] for l in range(size)) for i in range(size)]
     assert sum(v)==0 and sum(w)==0
     assert sum(abs(x) for x in w)<=theta*sum(abs(x) for x in v)
     assert all(sum(U[i][l] for i in range(size))==1 for l in range(size))
     n+=1
 counts['stochastic_contraction']=n
 n=0
 # Period-two alternating schedules have each window integral exactly one,
 # for rational start positions, independently of the starting phase.
 def integral(start,end,parity):
  total=F(0);x=start
  while x<end:
   j=x.numerator//x.denominator; z=min(end,F(j+1))
   if j%2==parity:total+=z-x
   x=z
  return total
 for denominator in range(1,18):
  for j in range(2*denominator):
   s=F(j,denominator)
   assert integral(s,s+2,0)==integral(s,s+2,1)==1;n+=1
 counts['periodic_pe_windows']=n
 n=0
 for j in range(1,64):
  t=F(j,128);x=2/(1-2*t);derivative=4/(1-2*t)**2
  assert derivative==x*x and 1/x==F(1,2)-t;n+=1
 counts['finite_time_blowup_identity']=n
 n=0
 # Exact time-ordered path term on disjoint windows is a rectangular product;
 # unlike simultaneous activation, it remains positive under separated slots.
 for rates in product([F(1,4),F(1,2),F(1)],repeat=4):
  window_masses=[2*r for r in rates]
  forward=F(1)
  for w in window_masses:forward*=w
  assert forward>=F(1,2)**4;n+=1
 counts['chronological_window_products']=n
 return dict(status='PASS',counts=counts,scope='Finite exact rational algebra only; no universal dynamics, contribution or priority certification')
if __name__=='__main__':
 import json
 print(json.dumps(run(),indent=2))
