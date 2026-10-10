"""Exact rational diagnostics. Reads prior diagnostics without writing them."""
from fractions import Fraction as F
from itertools import product,combinations
from collections import Counter
from pathlib import Path
import json,runpy,math
R=Path(__file__).resolve().parents[3]
def check():
 counts=Counter()
 def ck(group,v):
  assert v,group
  counts[group]+=1
 def dot(a,b):return sum((x*y for x,y in zip(a,b)),F(0))
 def mv(A,v):return [dot(row,v) for row in A]
 def mm(A,B):return [[dot(row,col) for col in zip(*B)] for row in A]
 def power(A,k):
  B=[[F(i==j) for j in range(len(A))] for i in range(len(A))]
  for _ in range(k):B=mm(B,A)
  return B
 def inner(pi,a,b):return sum((p*x*y for p,x,y in zip(pi,a,b)),F(0))
 # Nonuniform zero-field Gibbs laws: exp(H/2) is rational.
 spin=list(product([-1,1],repeat=3));N=len(spin);nu=[F(1,N)]*N;idx={x:i for i,x in enumerate(spin)}
 edges=list(combinations(range(3),2))
 for couplings in [(1,1,-1),(1,2,0),(-1,-2,1)]:
  half=[F(2)**sum(j*x[a]*x[b] for j,(a,b) in zip(couplings,edges)) for x in spin]
  weight=[x*x for x in half];zp=dot(nu,weight);zm=dot(nu,[1/w for w in weight]);pi=[nu[i]*weight[i]/zp for i in range(N)]
  L=[[F(0) for _ in spin] for _ in spin];A=[[F(0) for _ in spin] for _ in spin];U=[]
  for i,x in enumerate(spin):
   for site in range(3):
    y=list(x);y[site]*=-1;j=idx[tuple(y)]
    c=weight[j]/(weight[i]+weight[j]);aa=half[i]*half[j]/(weight[i]+weight[j])
    L[i][j]+=c;L[i][i]-=c;A[i][j]+=aa;A[i][i]-=aa
   U.append(-L[i][i]+A[i][i])
  S=[[half[i]*L[i][j]/half[j] for j in range(N)] for i in range(N)]
  for i in range(N):
   ck('generator_rows',sum(L[i])==0)
   for j in range(N):
    ck('detailed_balance',pi[i]*L[i][j]==pi[j]*L[j][i])
    ck('symmetric_conjugation',S[i][j]==S[j][i] and S[i][j]==A[i][j]-(U[i] if i==j else 0))
  K=[[F(i==j)+L[i][j]/3 for j in range(N)] for i in range(N)]
  for row in K:ck('heatbath_kernel',sum(row)==1 and min(row)>=0)
  w0=[nu[i]/pi[i] for i in range(N)];v=[1/h for h in half]
  ck('initial_partition_product',inner(pi,w0,w0)==zp*zm)
  for s in [1,2,4]:
   P=power(K,s);P2=mm(P,P);w=mv(P,w0);rho=[sum(nu[i]*P[i][j] for i in range(N)) for j in range(N)]
   D=inner(pi,w,w)
   ck('density_mass',dot(pi,w)==1 and all(rho[i]==pi[i]*w[i] for i in range(N)))
   ck('collision_representation',D==sum(rho[i]**2/pi[i] for i in range(N)))
   ck('reversed_endpoint_representation',D==zp*dot(nu,mv(P2,[1/x for x in weight])))
   P2sym=[[half[i]*P2[i][j]/half[j] for j in range(N)] for i in range(N)]
   ck('positive_quadratic_representation',D==zp*dot(nu,[v[i]*y for i,y in enumerate(mv(P2sym,v))]))
   m=D/zp
   for i in range(N):
    midpoint=rho[i]*dot(P[i],[1/x for x in weight])/m
    ck('square_tilted_midpoint',midpoint==pi[i]*w[i]**2/D)
    for j in range(N):
     ck('weighted_path_reversal',nu[i]*P2[i][j]/weight[j]/m==nu[j]*P2[j][i]/weight[i]/m)
   ck('density_contraction',1<=D<=zp*zm)
  # Four-time identity on a nonuniform stationary chain, arbitrary rational overlap scale.
  for t,u in [(1,1),(2,1),(1,2)]:
   Pt=power(K,t);Pu=power(K,u);P2u=mm(Pu,Pu)
   q=[[F(sum(x*y for x,y in zip(a,b)),4) for b in spin] for a in spin]
   f=[sum(Pt[i][j]*q[i][j] for j in range(N)) for i in range(N)]
   mean=dot(pi,f);g=[x-mean for x in f];profile=inner(pi,mv(Pu,g),mv(Pu,g))
   # Integrate the actual four-endpoint trajectory in full, without the claimed conditioning formula.
   four=sum(pi[i]*Pt[i][j]*P2u[j][k]*Pt[k][l]*q[i][j]*q[k][l]
            for i,j,k,l in product(range(N),repeat=4))
   ck('nonuniform_fourtime_centering',four-mean**2==profile)
   ck('positive_profile',profile>=0)
   ck('profile_contraction',inner(pi,mv(K,mv(Pu,g)),mv(K,mv(Pu,g)))<=profile)
 # Sign-changing Feynman-Kac potential and the two-spin decay eigenvector.
 pi=[F(2,5),F(1,10),F(1,10),F(2,5)];ss=list(product([-1,1],repeat=2));prodspin=[F(x*y) for x,y in ss]
 L=[[F(0) for _ in ss] for _ in ss]
 for i,x in enumerate(ss):
  c=F(1,5) if x[0]==x[1] else F(4,5)
  for k in range(2):
   y=list(x);y[k]*=-1;j=ss.index(tuple(y));L[i][j]=c;L[i][i]-=c
  ck('potential_sign',2*(c-F(2,5))==(F(-2,5) if x[0]==x[1] else F(4,5)))
 centered=[x-F(3,5) for x in prodspin]
 ck('two_spin_eigenvalue',mv(L,centered)==[-2*x for x in centered])
 w0=[F(1,4)/p for p in pi]
 ck('two_spin_square_coefficient',inner(pi,[w-1 for w in w0],[w-1 for w in w0])==F(9,16))
 # Initial Rad identity by exact formal polynomial in C=cosh(2/sqrt(n)).
 # Enumerate spin pairs, independently of the binomial grouping.
 for n in range(2,8):
  states=list(product([-1,1],repeat=n));ed=list(combinations(range(n),2));poly=Counter()
  for x in states:
   for y in states:
    degree=sum(x[i]*x[j]!=y[i]*y[j] for i,j in ed);poly[degree]+=1
  grouped=Counter()
  for k in range(n+1):grouped[k*(n-k)]+=math.comb(n,k)*2**n
  ck('rad_normalizer_polynomial',poly==grouped)
  ck('normalizer_probability_coefficients',sum(poly.values())==4**n)
  if n%2==0:ck('central_binomial_lower_bound',math.comb(n,n//2)*(n+1)>=2**n)
 # First-failure expansion including three complete roots (exact, no signed masses).
 for ws in product([F(1,4),F(2,3),F(4,5)],repeat=6):
  prefix=F(1);loss=F(0)
  for w in ws:loss+=prefix*(1-w);prefix*=w
  ck('first_failure_telescoping',loss==1-prefix and loss>=0)
 # Product refresh countermodel: lumped two-state coordinates retain exact full-state marginals.
 for m in range(2,42):
  p=F(1,2**m);q=F(1,m);stat=[1-p,p]
  for a in [F(1,2),F(2,3),F(3,4)]:
   K1=[[a*F(i==j)+(1-a)*stat[j] for j in range(2)] for i in range(2)]
   K2=[[a*a*F(i==j)+(1-a*a)*stat[j] for j in range(2)] for i in range(2)]
   pairs=list(product(range(2),repeat=2));P=[[K1[x][xx]*K2[y][yy] for xx,yy in pairs] for x,y in pairs]
   pp=[stat[x]*stat[y] for x,y in pairs];qq=[([1-q,q][x])*([1-q,q][y]) for x,y in pairs]
   f=[F(m*(x-y)) for x,y in pairs];Pf=mv(P,f)
   ck('fair_countermodel_centered',dot(pp,f)==0)
   ck('fair_countermodel_expectation',dot(qq,Pf)==(1-m*p)*(a-a*a))
   ck('fair_countermodel_profile',inner(pp,Pf,Pf)==m*m*p*(1-p)*(a*a+a**4))
   ck('fair_countermodel_reversible',all(pp[i]*P[i][j]==pp[j]*P[j][i] for i in range(4) for j in range(4)))
   if a==F(1,2):ck('fair_countermodel_bump',dot(qq,Pf)==(1-m*p)/4)
  ck('entropy_complement_negative',q>=p and (1-q)/(1-p)<=1)
  ck('entropy_main_coefficient',q*m==1)
  for k in range(1,9):ck('all_fixed_moment_formula',dot(pp,[abs(x)**k for x in f])==2*m**k*p*(1-p))
 for k in range(5,24):ck('replacement_powers',F(2)-F(k,2)+F(2,3)*F(k-4,2)==-F(k-4,6))
 ck('replacement_remainder',F(2)-F(24,6)==-2)
 ck('four_time_mesh_error',F(7,3)-4<0)
 prior=runpy.run_path(str(R/'frontier/experiments/i40_critical_sk_waiting_relaxation/check.py'))['check']()
 return {'status':'PASS exact finite diagnostics only','groups':dict(counts),'exact_assertions':sum(counts.values()),'replayed_i40_assertions':prior['exact_assertions'],'replayed_i39_assertions':prior['prior_exact_assertions'],'floating_diagnostics':False,'limitations':'Finite rational algebra is not an analytic proof review of R or a proof of Rademacher W. Discrete powers check semigroup identities; no rational claim about transcendental matrix exponentials.'}
if __name__=='__main__':print(json.dumps(check(),indent=2))
