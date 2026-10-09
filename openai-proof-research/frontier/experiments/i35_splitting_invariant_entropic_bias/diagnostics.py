"""Exact I35 diagnostics. No floating quadrature and no claim to certify analytic proofs."""
from pathlib import Path
from fractions import Fraction as F
import json
R=Path(__file__).resolve().parents[3]; E=R/'frontier/experiments/i35_splitting_invariant_entropic_bias'
def primes(n):
 out={};p=2
 while p*p<=n:
  while n%p==0:out[p]=out.get(p,0)+1;n//=p
  p+=1
 if n>1:out[n]=out.get(n,0)+1
 return out
def logadd(out,coef,x):
 x=F(x)
 for n,sgn in [(x.numerator,1),(x.denominator,-1)]:
  for p,k in primes(n).items():out[p]=out.get(p,F(0))+coef*sgn*k
 return {p:v for p,v in out.items() if v}
def kl(p,q):
 out={}
 for a,b in zip(p,q):
  if a:out=logadd(out,a,a/b)
 return out
def add(*terms):
 out={}
 for c,d in terms:
  for p,v in d.items():out[p]=out.get(p,F(0))+c*v
 return {p:v for p,v in out.items() if v}
def wt2(a,b):
 a=[[F(x),F(m)] for x,m in sorted(a) if m];b=[[F(x),F(m)] for x,m in sorted(b) if m];i=j=0;s=F(0)
 assert sum(m for x,m in a)==sum(m for x,m in b)==1
 while i<len(a) and j<len(b):
  t=min(a[i][1],b[j][1]);s+=t*(a[i][0]-b[j][0])**2;a[i][1]-=t;b[j][1]-=t
  if not a[i][1]:i+=1
  if not b[j][1]:j+=1
 return s
out={'scope':'Exact identities and stated analytic-enclosure certificates; finite algebra models are not continuous counterexamples.'}
chains=[]
for k in range(1,25):
 counts=[[2+k,3,5+k*k,7],[11,13+k,17,19+k]];tot=sum(map(sum,counts));P=[[F(a,tot) for a in row] for row in counts];rho=[sum(row) for row in P];m=[sum(row[i] for row in P) for i in range(4)];groups=[[0,1],[2,3]];M=[sum(m[i] for i in A) for A in groups];bar=[[sum(row[i] for i in A) for A in groups] for row in P];Q=[[bar[x][i//2]*m[i]/M[i//2] for i in range(4)] for x in range(2)]
 full=kl(sum(P,[]),[rho[x]*m[i] for x in range(2) for i in range(4)]);coarse=kl(sum(bar,[]),[rho[x]*M[a] for x in range(2) for a in range(2)]);internal=kl(sum(P,[]),sum(Q,[]));assert not add((1,full),(-1,coarse),(-1,internal))
 # Coincident splitting with nonuniform rational masses, exact source kernel.
 alpha=[F(1,k+3),F(2,k+3),F(k,k+3)];splitP=[];splitm=[]
 for i in range(4):splitm.extend([m[i]*v for v in alpha])
 for row in P:splitP.append([row[i]*v for i in range(4) for v in alpha])
 prob=[[v/rho[x] for v in row] for x,row in enumerate(P)];sp=[[v/rho[x] for v in row] for x,row in enumerate(splitP)]
 for x in range(2):
  for z in range(2):assert sum(prob[x][i]*prob[z][i]/m[i] for i in range(4))==sum(sp[x][i]*sp[z][i]/splitm[i] for i in range(12))
 chains.append({'k':k,'formal_chain_rule':'zero prime-log residual','unequal_split_kernel_entries':4})
out['chain_and_split']=chains
sym=[]
for r in [F(n,d) for d in range(1,5) for n in range(d+1,d+9)]:
 a=r/(1+r);P=[a/2,(1-a)/2,(1-a)/2,a/2];Q=[F(1,4)]*4;lhs=add((1,kl(P,Q)),(1,kl(Q,P)));rhs=logadd({},(2*a-1)/2,r);assert lhs==rhs;sym.append({'odds':str(r),'identity':'symmetric KL = centered correlation, epsilon=1','model':'two-point source, algebra diagnostic only'})
out['symmetric_gibbs_identity']=sym
spl=[]
for aa in [F(1,5),F(1,9),F(1,17),F(1,33),F(1,65)]:
 for div in [2,3,5,8]:
  b=aa/div;V=aa*b*b;B=b/4+V;Fc=b/4+b**3/4
  assert (B+Fc-V)**2<=4*B*Fc
  for y in [F(-1),F(-3,4),F(-1,2),F(0),F(1,3),F(1)]:
   h=aa+b*(abs(y)-F(1,2));a=[(-1,(1-aa)/2),(0,aa),(1,(1-aa)/2)];c=[(-1,(1-h)/2),(0,h),(1,(1-h)/2)];assert wt2(a,c)==abs(h-aa)
  spl.append(dict(a=str(aa),b=str(b),V=str(V),B=str(B),F1=str(b/4),F2=str(b**3/4),F_over_V=str(Fc/V),model='I34 admissible feasible plan; explicitly NOT Gibbs'))
out['split_center_fibers']=spl
# Prefix geometry over Q(sqrt(3)); coordinate tuple (x,y/sqrt(3)) for N=3,6.
rings={3:[(F(1),F(0)),(F(-1,2),F(1,2)),(F(-1,2),F(-1,2))],6:[(F(1),F(0)),(F(1,2),F(1,2)),(F(1,2),F(-1,2)),(F(-1,2),F(1,2)),(F(-1,2),F(-1,2)),(F(-1),F(0))],4:[(F(1),F(0)),(F(0),F(1)),(F(0),F(-1)),(F(-1),F(0))]}
prefix=[]
for N,pts in rings.items():
 for k in range(1,N+1):
  x=sum(p[0] for p in pts[:k])/k;y=sum(p[1] for p in pts[:k])/k;slack=x-x*x-(1 if N==4 else 3)*y*y;assert slack>=0;prefix.append(dict(N=N,k=k,disk_slack=str(slack)))
out['exact_polygon_prefix_geometry']=prefix
ps=[]
for N in range(2,130):
 weights=[F((N-i)**2) for i in range(N)];total=sum(weights);p=[w/total for w in weights]+[F(0)];lam=[(i+1)*(p[i]-p[i+1]) for i in range(N)];assert min(lam)>=0 and sum(lam)==1
 for j in range(N):assert sum(lam[k]/(k+1) for k in range(j,N))==p[j]
 ps.append({'N':N,'prefix_reconstruction':'exact'})
out['prefix_decompositions']=ps
# Rigorous log(2) enclosure from 2 sum_{n>=0} 3^{-(2n+1)}/(2n+1).
M=28;lo=2*sum(F(1,(2*n+1)*3**(2*n+1)) for n in range(M));hi=lo+F(9,4*(2*M+1)*3**(2*M+1));assert F(69,100)<lo<hi<F(70,100)
bs=[]
for k in range(9):
 eps=F(1,2**k);tail=F(1,2**int(4/eps));lower=2*(2*lo-1)-2*tail;upper=2*(2*hi-1);assert F(1,4)<lower<upper<1
 bs.append({'epsilon':str(eps),'true_B_over_epsilon_lower':str(lower),'true_B_over_epsilon_upper':str(upper),'certificate':'Equation (23), rational log2 interval, exp(-4/eps)<2^(-4/eps); exact nonproduct four-atom Gibbs example'})
out['true_gibbs_bias_enclosures']=bs
out['summary']={'entropy_chain_cases':len(chains),'unequal_split_kernel_entries':4*len(chains),'symmetric_Gibbs_KL_cases':len(sym),'split_center_fiber_cases':len(spl),'scalar_W2_checks':6*len(spl),'exact_polygon_prefix_cases':len(prefix),'prefix_decompositions':len(ps),'true_bias_enclosures':len(bs),'floating_quadrature':False}
(E/'diagnostics.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out['summary'],indent=2))
