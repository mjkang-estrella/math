import itertools,math,json,pathlib
from fractions import Fraction
P=pathlib.Path(__file__).resolve().parent

def mul(a,b,cap=None):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):
   if cap is None or i+j<=cap:c[i+j]+=x*y
 return c if cap is None else c[:cap+1]
def partitions(n,k,lo=0):
 if k==0:
  if n==0:yield ()
  return
 for a in range(lo,n//k+1):
  for tail in partitions(n-a,k-1,a):yield (a,)+tail
rows=[];tested=0
for r in range(2,6):
 M=r*(r-1); perms=list(itertools.permutations(range(r))); data=[]
 for q in perms:
  sign=(-1)**sum(q[i]>q[j] for i in range(r) for j in range(i+1,r));z=[sign]
  for i in range(r):
   for k in range(2*(q[i]-i)+1,2*(r-1-i)+1):z=mul(z,[1,k])
  data.append(([2*(q[i]-i+r-1) for i in range(r)],z))
 local=0;max_m=M-1 if r<=4 else 6
 for m in range(max_m+1):
  for a in partitions(m,r):
   orbit=set(itertools.permutations(a));c=[0]*(M+1)
   for e,z in data:
    weight=sum(math.prod(math.comb(ei,ai) if ai<=ei else 0 for ei,ai in zip(e,aa)) for aa in orbit)
    for i,zi in enumerate(z):c[i]+=weight*zi
   for i,ci in enumerate(c):
    if m+2*i<M:
     assert ci==0,(r,m,a,i,ci);local+=1
 rows.append({'r':r,'checked_m_through':max_m,'zero_coefficient_obligations':local,'full_stronger_forbidden_region':r<=4});tested+=local
# Independent polynomial implementation of the literal CV recurrence and Hankel determinants.
import sympy as s
y=s.symbols('y');D=lambda f:s.expand(4*y*s.diff(f,y));p=[2*y-3]
for k in range(12):p.append(s.expand(D(p[-1])+(5-4*y)*p[-1]))
W=[s.Integer(1),p[0]];wr=[]
for r in range(1,8):
 if r>=2:
  prev=W[-1];num=s.expand(prev*D(D(prev))-D(prev)**2-16*(r-1)*y*prev**2)
  quo,rem=s.div(num,W[-2],y);assert rem==0;W.append(s.expand(quo))
 pol=s.Poly(W[r],y);assert pol.degree()==r*(r+1)//2
 assert (-1)**(r*(r-1)//2)*pol.LC()>0
 if r<=4:assert s.expand(s.det(s.Matrix(r,r,lambda i,j:p[i+j]))-W[r])==0
 wr.append({'r':r,'degree':pol.degree(),'leading':str(pol.LC()),'literal_determinant_compared':r<=4})
# Falsify the too-strong claim of vanishing on the boundary m+2i=M.
# r2,y0 has -(t1^2-t2^2)^2/2, coefficient x1^2=-2.
assert sum(z[0]*math.comb(e[0],2) for e,z in [([2*(q[i]-i+1) for i in range(2)], [(-1)**(q[0]>q[1])]) for q in itertools.permutations(range(2))])!=0
out={'vanishing':rows,'total_zero_checks':tested,'CV_Wronskians':wr,'boundary_nonvanishing_r2_y0_x1_squared':'-2 after symmetrization','status':'finite exact diagnostics, not novelty evidence'}
(P/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
