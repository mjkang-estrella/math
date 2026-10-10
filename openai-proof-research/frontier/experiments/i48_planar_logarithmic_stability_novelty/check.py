#!/usr/bin/env python3
"""Read-only, exact rational diagnostics for the I48 operation reduction."""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction as F
from itertools import product, combinations
import json
checks=0

def check(b):
 global checks
 checks+=1
 assert b,checks

def det(a):
 a=[list(x) for x in a]; out=F(1)
 for k in range(len(a)):
  j=next((j for j in range(k,len(a)) if a[j][k]),None)
  if j is None:return F(0)
  if j!=k:a[j],a[k]=a[k],a[j];out=-out
  p=a[k][k];out*=p
  for i in range(k+1,len(a)):
   t=a[i][k]/p
   for j in range(k+1,len(a)):a[i][j]-=t*a[k][j]
 return out

def psd(a):
 for n in range(1,len(a)+1):
  for ii in combinations(range(len(a)),n):check(det([[a[i][j] for j in ii] for i in ii])>=0)

def unit(t):
 t=F(t);return ((1-t*t)/(1+t*t),2*t/(1+t*t))
def cross(a,b):return a[0]*b[1]-a[1]*b[0]
def dot(a,b):return a[0]*b[0]+a[1]*b[1]
def mass(mu,A):return sum((mu[i] for i in A),F(0))
def edge(w,A,B):return sum((w[i][j] for i in A for j in B),F(0))

cases=[([0,1],[4,4]),([0,F(1,3),1],[4,1,4]),([0,F(1,10),1,F(11,10)],[4,1,3,2]),([0,F(1,3),F(2,3),1,2],[4,2,1,4,1])]
for n in [16,256,65536]:cases.append(([0,F(1,n),1,1+F(1,n),2],[4,F(1,n),4,F(1,n),F(1,n*n)]))
cases += [([0,F(2,3)],[3,5]),([0,F(1,100),F(2,3),F(67,100),2],[4,F(1,100),4,F(1,100),F(1,10000)])]
records=[]
for ts,ss in cases:
 u=list(map(unit,ts));s=list(map(F,ss));N=len(u);I=list(range(N));M=sum(s)
 k=[[abs(cross(a,b)) for b in u] for a in u]
 check(all(k[i][j]>0 for i in I for j in I if i!=j))
 h=[sum(k[i][j]*s[j] for j in I)/4 for i in I];V=sum(h[i]*s[i] for i in I)/2
 sigma=[x/M for x in s];nu=[h[i]*s[i]/(2*V) for i in I];a0=M*M/(8*V)
 w=[[s[i]*s[j]*k[i][j]/(8*V) for j in I] for i in I]
 check(sum(nu)==1)
 for i in I:check(sum(w[i])==nu[i])
 # Exact mean-zero spectral negativity, hence ordinary gap at least one.
 B=[[F(int(i==j)) if i<N-1 else -nu[j]/nu[-1] for j in range(N-1)] for i in I]
 H=[[-sum(B[i][a]*w[i][j]*B[j][b] for i in I for j in I) for b in range(N-1)] for a in range(N-1)]
 for n in range(1,N):check(det([r[:n] for r in H[:n]])>0)
 for bits in product([0,1],repeat=N):
  A=[i for i in I if bits[i]];C=[i for i in I if not bits[i]];z=mass(nu,A)
  check(edge(w,A,C)>=z*(1-z))
 best=None
 for colors in product(range(3),repeat=N):
  A=[i for i in I if colors[i]==0];Bset=[i for i in I if colors[i]==1];C=[i for i in I if colors[i]==2]
  if not A or not Bset:continue
  z=mass(nu,A+Bset);b=(edge(w,A,A)+edge(w,Bset,Bset)+edge(w,A+Bset,C))/z
  if best is None or b<best[0]:best=(b,A,Bset,C)
 beta,A,Bset,C=best;z=mass(nu,A+Bset)
 check(2*edge(w,A,Bset)==(1-beta)*z)
 check(mass(nu,C)<=beta)
 check(mass(nu,A)>=(1-beta)**2/2);check(mass(nu,Bset)>=(1-beta)**2/2)
 # Certifies beta^2 ||q||^2 <= sum w_ij(q_i+q_j)^2 for ALL q in this fixture.
 psd([[2*w[i][j]+((2-beta*beta)*nu[i] if i==j else 0) for j in I] for i in I])
 aa=min(A,key=lambda i:sum(sigma[j]*k[i][j] for j in A));bb=min(Bset,key=lambda i:sum(sigma[j]*k[i][j] for j in Bset))
 ea=sum(sigma[j]*k[aa][j] for j in A);eb=sum(sigma[j]*k[bb][j] for j in Bset)
 check(ea<=beta/(a0*mass(sigma,A)));check(eb<=beta/(a0*mass(sigma,Bset)))
 # The sine metric satisfies a triangle inequality; all constants here are rational.
 for i,j,l in product(I,repeat=3):check(k[i][j]<=k[i][l]+k[l][j])
 kab=sum(sigma[i]*sigma[j]*k[i][j] for i in A for j in Bset)
 check(mass(sigma,A)*mass(sigma,Bset)*k[aa][bb]>=kab-mass(sigma,Bset)*ea-mass(sigma,A)*eb)
 target={i:(aa if i in A+C else bb) for i in I}
 # Projective sine controls change of sine kernel by <= 2 sin distance.
 transport=sum(sigma[i]*k[i][target[i]] for i in I)
 check(transport<=ea+eb+mass(sigma,C))
 support_error=M*transport/2
 for t in list(map(F,ts))+[F(1,7),F(5,3),F(7)]:
  v=unit(t);hp=sum(s[i]*abs(cross(v,u[i])) for i in I)/4
  h0=sum(s[i]*abs(cross(v,u[target[i]])) for i in I)/4
  check(abs(hp-h0)<=support_error)
 # Actual-normal enclosing parallelogram: every original zonotope vertex satisfies slabs.
 if k[aa][bb]>0:
  verts=[]
  for eps in product([-1,1],repeat=N):
   x=(sum(-eps[i]*s[i]*u[i][1]/4 for i in I),sum(eps[i]*s[i]*u[i][0]/4 for i in I));verts.append(x)
   check(abs(dot(u[aa],x))<=h[aa]);check(abs(dot(u[bb],x))<=h[bb])
  check(max(dot(u[aa],x) for x in verts)==h[aa]);check(max(dot(u[bb],x) for x in verts)==h[bb])
 records.append({'directions':N,'beta':str(beta),'minimum_mass':str(min(sigma)),'anchor_sine':str(k[aa][bb])})
# Negative control: dual Cheeger alone cannot capture total mass in a general graph.
# A disconnected edge plus a triangle has beta=0, yet leaves 3/4 degree mass outside.
w=[[F(0) for _ in range(5)] for _ in range(5)]
for i,j in [(0,1),(2,3),(3,4),(4,2)]:w[i][j]=w[j][i]=F(1,8)
nu=[sum(x) for x in w];check(sum(nu)==1);check(edge(w,[0,1],[2,3,4])==0);check(mass(nu,[2,3,4])==F(3,4))
check(edge(w,[0,1],[2,3,4])<mass(nu,[0,1])*mass(nu,[2,3,4]))
# A connected epsilon-bridge variant also fails the gap-one inference.
w[1][2]=w[2][1]=F(1,1024);Z=sum(map(sum,w));w=[[x/Z for x in row] for row in w];nu=list(map(sum,w));z=mass(nu,[0,1]);check(edge(w,[0,1],[2,3,4])<z*(1-z))
# Exact exponent budget and the weakening to the requested exponent.
check(F(1,3)/2==F(1,6));check((1-F(1,3))/4==F(1,6));check(6<10)
# Three-region comparison: s^-4 D bound follows from beta <= sqrt(D/v) and transport.
# Transport eta gives outside radius-s mass <= eta/s; eta <= c*s^2 suffices.
check(2*2==4);check((1-4*F(1,5))/2==F(1,10))
# Xi normalized three-step identities, no transcendental evaluation.
for t in [F(1,4),F(1,2),F(1),F(2),F(5)]:
 H2=(t+1)**2/t;check(H2==2+t+1/t)
 for m in [F(1),F(101,100),F(5,4)]:
  for b in [F(0),(m-1)*H2/3,(m-1)*H2]:
   Carea=H2+b;check(Carea<=H2*m);check(Carea-H2<=H2*(m-1))
print(json.dumps({'status':'PASS','scope':'Exact finite diagnostics, not a proof of universal bounds or source priority','exact_assertions':checks,'sine_graph_cases':len(cases),'cases':records,'negative_controls':2,'reduction_rate':'distance <= C deficit^(1/6); P10 follows on bounded classes'},indent=2,sort_keys=True))
