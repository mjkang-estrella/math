"""Read-only exact algebra and separately labeled floating diagnostics."""
from fractions import Fraction as F
from math import factorial, prod, log, exp, sqrt, lgamma, pi
import json, random
import math as mp
mp.mpf=float
mp.loggamma=mp.lgamma
def digamma(x):
 value=0.0
 while x<24:
  value-=1/x; x+=1
 z=1/(x*x)
 return value+log(x)-1/(2*x)-z*(1/12-z*(1/120-z*(1/252-z*(1/240-z*(1/132-z*691/32760)))))
mp.digamma=digamma

checks=0
def check(ok):
 global checks
 assert ok
 checks+=1
def indices(m,k):
 if m==1:
  yield (k,); return
 for a in range(k+1):
  for b in indices(m-1,k-a): yield (a,)+b
def add(p,a,c):
 p[a]=p.get(a,F(0))+c
def deriv(p,j):
 out={}
 for a,c in p.items():
  if a[j]:
   b=list(a); b[j]-=1; add(out,tuple(b),c*a[j])
 return out
def norm(p): return sum(c*c*prod(factorial(v) for v in a) for a,c in p.items())
def sub(p,q):
 out=dict(p)
 for a,c in q.items(): add(out,a,-c)
 return out
rng=random.Random(590053)
hodge_cases=0
for m in range(1,6):
 for k in range(0,6):
  for trial in range(3):
   V=[{a:F(rng.randrange(-4,5),3) for a in indices(m,k)} for j in range(m)]
   u={}
   for j in range(m):
    for a,c in V[j].items():
     b=list(a); b[j]+=1; add(u,tuple(b),c/F(k+1))
   projection=[deriv(u,j) for j in range(m)]
   defect=sum(norm(sub(V[j],projection[j])) for j in range(m))
   curls=sum(norm(sub(deriv(V[s],r),deriv(V[r],s))) for r in range(m) for s in range(r+1,m))
   check(curls==F(k+1)*defect)
   check(sum(norm(v) for v in V)==sum(norm(v) for v in projection)+defect)
   hodge_cases+=1
for d in range(2,1001):
 u=F(1,d); Q=F(43,100)+F(26,100)*(u-F(1,2))+F(68,25)*(u-F(1,2))**2
 coefficient=d-1-F(69,500)-d*Q
 extra=F((d-2)*(d+68),50*d)
 check(coefficient==F(1,500)+extra)
 check(coefficient>=F(d,1000))
for m in range(1,101):
 # Dirichlet(1,...,1) angular covariance and exact independent-radius cost.
 eu2=F(2,m*(m+1)); euu=F(1,m*(m+1)); mean=F(1,m)
 check(m*(eu2-mean**2)==F(m-1,m*(m+1)))
 for a in [m,2*m,10*m]:
  es=F(a); es2=F(a*(a+1)); var=F(a)
  check(var<=es**2/m)
  ct=es2*(eu2-euu); cr=var/m
  check(ct==F(a*(a+1),m*(m+1)))
  check(cr==F(a,m))
 # Uniform simplex radial S~Beta(m,1).
 es=F(m,m+1); es2=F(m,m+2); var=es2-es**2
 check(var==F(m,(m+1)**2*(m+2)))
 check(var<=es**2/m)

# Spin-factor tensor, use rational amplitude 1 first; rescaling by 1/sqrt(2)
# gives B=diag((m-1)/2,1,...,1). All tensor support and energy counts exact.
for m in range(2,30):
 entries={(i,j,k):F(int((i==0 and j==k and j>0) or (j==0 and i==k and i>0) or (k==0 and i==j and i>0)))
          for i in range(m) for j in range(m) for k in range(m)}
 for i,j,k in entries:
  check(entries[i,j,k]==entries[j,i,k]==entries[k,j,i])
 B=[sum(entries[i,j,r]**2 for j in range(m) for r in range(m))/2 for i in range(m)]
 check(B==[F(m-1,2)]+[F(1)]*(m-1))
 check(sum(entries[i,0,r]**2 for i in range(1,m) for r in range(m))/2==F(m-1,2))
 check(sum(entries.values())/2==F(3*(m-1),2))

channel_cases=0
for m in range(1,6):
 for trial in range(4):
  unordered={tuple(sorted((i,j,k))):F(rng.randrange(-3,4),2) for i in range(m) for j in range(m) for k in range(m)}
  T=lambda i,j,k:unordered[tuple(sorted((i,j,k)))]
  B=[[sum(T(i,j,r)*T(j,k,r) for j in range(m) for r in range(m)) for k in range(m)] for i in range(m)]
  for r in range(m):
   for s in range(m):
    check(sum(T(i,j,r)*T(i,j,s) for i in range(m) for j in range(m))==B[r][s])
  channel=0
  for a in range(m):
   for b in range(m):
    for c in range(m):
     for d in range(m):
      phi=sum(T(a,c,r)*T(d,b,r) for r in range(m))
      projection=sum(T(a,b,r)*T(c,d,r) for r in range(m))
      channel+=(phi-projection)**2
  comm=sum((sum(T(a,c,r)*T(c,b,s)-T(a,c,s)*T(c,b,r) for c in range(m)))**2
           for a in range(m) for b in range(m) for r in range(m) for s in range(m))
  check(channel==comm)
  channel_cases+=1

def radial_gamma(m,a):
 m,a=mp.mpf(m),mp.mpf(a)
 hx=a+mp.loggamma(a)+(m-a)*mp.digamma(a)-mp.loggamma(m)
 ct=a*(a+1)/(m*(m+1)); cr=a/m
 delta=0.0 if a==m else hx-(m-1)*mp.log(ct)/2-mp.log(cr)/2-m
 # Actual independent-radius/common-angle coupling cost; certified by formula in report.
 cost=2+2*(m-1)*(1-mp.sqrt(m*a/((m+1)*(a+1))))
 return float(delta),float(cost)
def simplex(m):
 m=mp.mpf(m)
 delta=-mp.loggamma(m+1)+(m+1)*mp.log(m+1)/2+m*mp.log(m+2)/2-m
 es=m/(m+1); es2=m/(m+2)
 cost=2+2*(m-1)*(1-mp.sqrt(m/(m+1))*es/mp.sqrt(es2))
 return float(delta),float(cost)
families=[]
for m in [1,2,8,32,128,512,2048]:
 for factor in [1,2,10]:
  gap,cost=radial_gamma(m,factor*m)
  families.append(dict(family='radial_gamma',m=m,a=factor*m,delta=gap,normalized_delta=gap/m,analytic_coupling_cost_float=cost,cost_per_dimension=cost/m))
 gap,cost=simplex(m)
 families.append(dict(family='uniform_simplex',m=m,delta=gap,normalized_delta=gap/m,analytic_coupling_cost_float=cost,cost_per_dimension=cost/m))
 # Actual cone law over cube, source identity (dimension m+1).
 n=mp.mpf(m); logLd=mp.loggamma(n+1)/n-(n+1)*mp.log(n+1)/(2*n)-mp.log(n+2)/2
 gap=n*(logLd+mp.log(12)/2)
 families.append(dict(family='cube_cone',m=m+1,delta=float(gap),normalized_delta=float(gap/(m+1))))
for m in [8,32,128,512]:
 a=1/sqrt(m)
 gap=m*(log(1+a)-log(1+a*a)/2); cost=m*(2-2/sqrt(1+a*a))
 families.append(dict(family='asymmetric_laplace_product',m=m,a=a,delta=gap,normalized_delta=gap/m,analytic_coupling_cost_float=cost,cost_per_dimension=cost/m))
 # Truncated exponential midpoint quantile integration; not certified.
 R=log(m)+2; z=1-exp(-R); mu=1-R/(exp(R)-1); sd=sqrt(1-R*R*exp(R)/(exp(R)-1)**2)
 gap1=log(z)+mu-log(sd)-1
 vals=[]
 for N in [4096,16384]:
  val=0
  for i in range(N):
   u=(i+.5)/N
   x=(-log(1-z*u)-mu)/sd; y=-log(1-u)-1
   val+=(x-y)**2/N
  vals.append(val)
 families.append(dict(family='truncated_exponential_product',m=m,R=R,delta=m*gap1,normalized_delta=gap1,uncertified_quantile_cost_per_dimension=vals))
 # Uniform positive orthant l_p ball: exact gamma-integral moment formulas, floating evaluation.
 n=mp.mpf(m); p=1+1/mp.sqrt(n)
 def moment(k): return exp(mp.lgamma((k+1)/p)-mp.lgamma(1/p)+mp.lgamma(1+n/p)-mp.lgamma(1+(n+k)/p))
 a1,a2=moment(1),moment(2)
 a11=exp(2*(mp.lgamma(2/p)-mp.lgamma(1/p))+mp.lgamma(1+n/p)-mp.lgamma(1+(n+2)/p))
 ct=a2-a11; cr=a2+(n-1)*a11-n*a1*a1
 volume=n*mp.loggamma(1+1/p)-mp.loggamma(1+n/p)
 gap=volume-((n-1)*mp.log(ct)+mp.log(cr))/2-n
 families.append(dict(family='positive_lp_ball',m=m,p=float(p),delta=float(gap),normalized_delta=float(gap/n),tangential_covariance=float(ct),radial_covariance=float(cr)))

def omega(v):
 return 3*(v-1)**2/(37+3*v)*(.15+.49*37/(37+3*v))*min(.13,1.28/sqrt(v))
heavy=[]
for m in [16,256,4096,65536]:
 v=m**1.5; s=1/(.925+.075*v)
 heavy.append(dict(m=m,normalized_omega=omega(v)/m,normalized_trace=(v+m-1)/m,regularized_heavy_energy=s*v,rank_fraction=1/m))

psi2=digamma(2)
first_conditional_gap=1-psi2-log(2)/2
second_conditional_gap=log(12)/2-1
log_variance_correction=psi2-log(6)/2
conditional=dict(first_gap=first_conditional_gap,second_gap=second_conditional_gap,
 log_variance_correction=log_variance_correction,
 sum=first_conditional_gap+second_conditional_gap+log_variance_correction,
 scope='Actual orthogonally rotated two-exponential equality law, not a U counterexample.')

print(json.dumps(dict(exact_assertions=checks,hodge_cases=hodge_cases,channel_cases=channel_cases,
 floating_label='Rounded analytic expressions and explicitly uncertified numerical quadrature; no universal inference.',
 families=families,conditional_equality_obstruction=conditional,
 abstract_not_density_heavy_examples=heavy),indent=2,sort_keys=True))
