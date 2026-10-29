from fractions import Fraction as F
from math import factorial
import json,pathlib
b=pathlib.Path(__file__).parent
n=12;t=F(48,5);r=F(23,20);s=r*t;K=80
lam=[F(1,10)+F(1,20)*(1-F(min(i,n-i),3)) for i in range(n)]
mean=sum(lam)/n;pi=[F(1,n)]*n;alpha=[x/(n*mean) for x in lam];w=[pi[i]-alpha[i] for i in range(n)]
assert mean==F(1,10) and min(lam)==F(1,20) and max(lam)==F(3,20)
# P=I+C/r has offdiag 1/r, diagonal (max(lam)-lam_i)/r.
diag=[(max(lam)-x)/r for x in lam]
assert all(0<=d and d+1/r<=1 for d in diag)
v=[F(1)]*n;S=F(0);weight=F(1);terms=[]
for k in range(K+1):
 term=weight*sum(w[i]*v[i] for i in range(n));S+=term;terms.append(term)
 v=[v[(i+1)%n]/r+diag[i]*v[i] for i in range(n)]
 weight*=s/F(k+1)
L=sum(abs(x) for x in w)
B=L*s**(K+1)/factorial(K+1)/(1-s/F(K+2))
assert S < -2 and B < F(1,100)
# Two independent exact formulations: direct Taylor for C, with norm bound.
u=[F(1)]*n;T=F(0);weight=F(1);J=160
for k in range(J+1):
 T+=weight*sum(w[i]*u[i] for i in range(n))
 u=[u[(i+1)%n]-(1+lam[i])*u[i] for i in range(n)]
 weight*=t/F(k+1)
z=t*(2+max(lam));BT=L*z**(J+1)/factorial(J+1)/(1-z/F(J+2))
assert T+BT < -F(1,25000)
# Source PH moment check c^2>=1 using exact Gauss elimination.
def solve(A,y):
 a=[list(row)+[yy] for row,yy in zip(A,y)]
 for j in range(n):
  h=next(i for i in range(j,n) if a[i][j]);a[j],a[h]=a[h],a[j]
  d=a[j][j];a[j]=[v/d for v in a[j]]
  for i in range(n):
   if i!=j:
    d=a[i][j];a[i]=[x-d*y for x,y in zip(a[i],a[j])]
 return [row[-1] for row in a]
A=[[((1+lam[i]) if i==j else F(0))-(1 if j==(i+1)%n else 0) for j in range(n)] for i in range(n)]
a=solve(A,[F(1)]*n);aa=solve(A,a)
mu=sum(alpha[i]*a[i] for i in range(n));second=2*sum(alpha[i]*aa[i] for i in range(n));scv=second/mu**2-1
assert mu==10 and scv>1
out={'status':'PASS','n':n,'t':str(t),'rates':list(map(str,lam)),'pi':list(map(str,pi)),'alpha':list(map(str,alpha)),'uniformization_rate':str(r),'s':str(s),'K':K,'signed_partial_sum':str(S),'tail_bound':str(B),'partial_sum_lt_minus2':S<-2,'tail_lt_1_over_100':B<F(1,100),'direct_taylor_order':J,'direct_taylor_sum':str(T),'direct_taylor_tail':str(BT),'survival_gap_lt_minus_1_over_25000':T+BT<-F(1,25000),'event_mean':str(mu),'event_scv':str(scv),'method':'Exact Fraction arithmetic; numerical decimals are not proof.'}
(b/'check-results.json').write_text(json.dumps(out,indent=2));print(json.dumps({k:v for k,v in out.items() if k not in ['signed_partial_sum','tail_bound','direct_taylor_sum','direct_taylor_tail','event_scv','pi','alpha']},indent=2))
