"""Exact finite diagnostics; not a proof by enumeration or an SK simulation."""
from fractions import Fraction as F
from itertools import product
import json,runpy
from pathlib import Path

def check():
 counts={}
 def ck(ok,group):
  if not ok:raise AssertionError(group)
  counts[group]=counts.get(group,0)+1
 states=list(product([-1,1],repeat=3));N=len(states)
 def kernel(a,b,c):return [[F(1+a*x[0]*y[0],2)*F(1+b*x[1]*y[1],2)*F(1+c*x[2]*y[2],2) for y in states] for x in states]
 def mv(A,v):return [sum(x*y for x,y in zip(row,v)) for row in A]
 def dot(v,w):return sum(x*y for x,y in zip(v,w))/N
 f=[F(z*(1+x+y),3) for x,y,z in states];h0=[1+F(x-y,4) for x,y,z in states]
 alpha=F(1,4)
 # t=-size*log(u), s=k*t: every rational kernel lies on the SAME
 # continuous-time generator with coordinate decay rates 1/size,2/size,1.
 for size,u,k in product([1,2,5],[F(1,5),F(1,2),F(4,5)],[1,2,3]):
  v=u**size;q=u**k;wz=v**k
  P=kernel(u,u*u,v);W=kernel(q,q*q,wz);ws=mv(W,h0)
  for i in range(N):
   ck(sum(P[i])==1,'stochastic_rows');ck(ws[i]==1+alpha*q*states[i][0]-alpha*q*q*states[i][1],'density_evolution')
   ck(F(1,2)<=ws[i]<=F(3,2),'density_bounds')
   for j in range(N):ck(0<=P[i][j]<=1 and P[i][j]==P[j][i],'positive_reversible_kernel')
  ck(dot(ws,[F(1)]*N)==1,'density_mass')
  pf=mv(P,f);Ft=[x*y for x,y in zip(f,pf)];A=dot(f,pf);B=dot(ws,Ft)
  ck(A==v*(1+u+u*u)/9,'stationary_formula')
  ck(B-A==alpha*v*((1+u)*q-(1+u*u)*q*q)/9,'delayed_bump_formula')
  for i,(x,y,z) in enumerate(states):
   ck(Ft[i]==v*(1+u+u*u+(1+u)*x+(1+u*u)*y+(u+u*u)*x*y)/9,'product_observable_expansion')
  G=[x-A for x in Ft];expected=v*v*((1+u)**2+(1+u*u)**2+(u+u*u)**2)/81
  ck(dot(G,G)==expected,'hidden_observable_variance')
  ck(B-A==dot([x-1 for x in h0],mv(W,G)),'reversible_duality')
  WG=mv(W,G);W2=kernel(q*q,q**4,wz*wz)
  ck(dot(WG,WG)==dot(G,mv(W2,G)),'positive_spectral_profile')
  ck(dot(WG,WG)<=dot(G,G),'L2_contraction')
  ck((B-A)**2<=dot([x-1 for x in h0],[x-1 for x in h0])*dot(WG,WG),'duality_Cauchy_Schwarz')
  # Direct path sum with first/last lag P, middle W2, endpoints f(X0)f(X1)f(X2)f(X3).
  four=sum(P[i][j]*W2[j][k]*P[k][l]*f[i]*f[j]*f[k]*f[l] for i,j,k,l in product(range(N),repeat=4))/N
  ck(four-A*A==dot(WG,WG),'four_time_identity')
  # Any signed two-copy tail: test cross-coordinate sum with cancellations.
  tail=[[F(x[0]*y[0]+x[1]*y[1]) for y in states] for x in states]
  tailF=[sum(P[i][j]*tail[i][j] for j in range(N)) for i in range(N)]
  energy=sum(P[i][j]*tail[i][j]**2 for i,j in product(range(N),repeat=2))/N
  V=sum(z*z for row in tail for z in row)/(N*N)
  ck(dot(tailF,tailF)<=energy<=8*V,'Jensen_kernel_tail')
 # Exact limiting coefficients: u->1, waiting attenuation q=1/2.
 ck(alpha*F(1,9)*(2*F(1,2)-2*F(1,4))==F(1,72),'bump_limit_coefficient')
 ck(F(12,81)==F(4,27),'hidden_limit_variance')
 for k in range(1,81):
  m=2**k;p=F(1,m**3);r=F(1,m);w=r/p;wc=(1-r)/(1-p)
  ck(p*w+(1-p)*wc==1 and w>0 and 0<wc<1,'spike_density_admissibility')
  ck(r*m==1 and p*m==F(1,m*m) and p*m*m==F(1,m),'spike_pairings')
  ck(p*w*w+(1-p)*wc*wc==m+(1-F(1,m))**2/(1-F(1,m**3)),'spike_L2')
  # D <= r log(w) = 2 k log(2)/2^k <= 2k/2^k; log2<=1 from integral.
  ck(w==2**(2*k) and F(2*k,m)>0,'spike_entropy_upper_coefficient')
  n=m**3;T=m*m
  ck(n*n==T**3 and F(1,T)*n==m and n*T==m**5,'site_attempt_clock_and_trace_units')
 for order in range(5,24):
  ck(F(2)-F(order,2)+F(2,3)*F(order-4,2)==-F(order-4,6),'replacement_exponent')
 ck(F(2)-F(24,2)+F(2,3)*F(24,2)==-2,'replacement_remainder')
 # Executed in memory: prior program writes nothing.
 prior=runpy.run_path(str(Path(__file__).resolve().parents[3]/'frontier/experiments/i39_quantum_spectral_discovery/check.py'))['check']()
 ck(prior['exact_assertions']==389,'prior_replay')
 return {'status':'PASS exact rational diagnostics only','groups':counts,'exact_assertions':sum(counts.values()),'cases_8_state':27,'prior_exact_assertions':prior['exact_assertions'],'floating_diagnostics':False,'scope':'Finite algebra, admissibility and normalization only; no independent proof review or substantial finding.'}
if __name__=='__main__':print(json.dumps(check(),indent=2))
