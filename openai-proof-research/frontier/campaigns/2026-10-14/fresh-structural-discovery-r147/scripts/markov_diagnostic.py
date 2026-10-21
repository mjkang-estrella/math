"""Finite exact checks only; no proof or novelty gate. Writes only to stdout."""
from fractions import Fraction as F
from itertools import product,combinations
import json

def mul(x,y,N):
 z=[F(0)]*(N+1)
 for i,v in enumerate(x):
  for j,w in enumerate(y):
   if i+j<=N:z[i+j]+=v*w
 return z

def kernels(a,b,N,start):
 P=((1-a,a),(b,1-b)); v=[[F(start[0])],[F(start[1])]]; out=[]
 for m in range(N+1):
  out.append([sum(v[s][j]*P[s][1] for s in (0,1)) for j in range(m+1)])
  z=[[F(0)]*(m+2) for _ in range(2)]
  for s in (0,1):
   for t in (0,1):
    for j,w in enumerate(v[s]):z[t][j+t]+=w*P[s][t]
  v=z
 return out

count=0
for a,b in [(F(1,5),F(1,5)),(F(4,5),F(4,5)),(F(2,7),F(3,7)),(F(2,5),F(3,5))]:
 pi=(b/(a+b),a/(a+b));P=((1-a,a),(b,1-b))
 AA=kernels(a,b,7,pi);BB=kernels(a,b,7,(0,1))
 for n in range(1,8):
  laws=[]
  for mask in product((0,1),repeat=n):
   prob=pi[mask[0]]
   for j in range(1,n):prob*=P[mask[j-1]][mask[j]]
   laws.append((mask,prob))
  assert sum(p for _,p in laws)==1
  for k in range(1,min(n,3)+1):
   for pos in combinations(range(n),k):
    actual={}
    for mask,prob in laws:
     if all(mask[j] for j in pos):
      counts=(sum(mask[:pos[0]]),)+tuple(sum(mask[pos[j]+1:pos[j+1]]) for j in range(k-1))
      actual[counts]=actual.get(counts,F(0))+prob
    polynomials=[AA[pos[0]]]+[BB[pos[j+1]-pos[j]-1] for j in range(k-1)]
    expected={}
    for ranks in product(*(range(len(q)) for q in polynomials)):
     val=F(1)
     for q,j in zip(polynomials,ranks):val*=q[j]
     if val:expected[ranks]=val
    assert actual==expected,(a,b,n,pos)
    count+=1
 # Check the scalar rational generating function recurrence for B_m.
 A=1-a;B=1-b;c=1-a-b
 for m in range(2,8):
  lhs=BB[m];rhs=[F(0)]*(m+1)
  for j,v in enumerate(BB[m-1]):rhs[j]+=A*v;rhs[j+1]+=B*v
  for j,v in enumerate(BB[m-2]):rhs[j+1]-=c*v
  assert lhs==rhs

a=b=F(4,5);B=1-b;N=16
BB=kernels(a,b,N,(0,1))
weights=[]
for m in range(N+1):
 weights.append((1-sum(BB[m][j]*weights[j] for j in range(m)))/BB[m][m])
assert weights[:3]==[5,-55,1805]
# General renewal thinning: triangular composition inversion to order 12.
r=F(1,10);N=12
g=[F(0),B]+[a*b*(1-a)**(j-2) for j in range(2,N+1)]
powers=[[F(1)]+[F(0)]*N]
for j in range(N):powers.append(mul(powers[-1],g,N))
h=[F(0)]*(N+1)
for m in range(1,N+1):
 h[m]=(r*(1-r)**(m-1)-sum(h[j]*powers[j][m] for j in range(1,m)))/powers[m][m]
assert h[1]==F(1,2) and h[2]==-F(23,4)
assert h[2]==r*((1-r)*B-a*b)/B**3
# Nearest discriminant root R=31-8sqrt(15) lies in (1/63,1/61).
# f(t)=t^2-62t+1 decreases there and vanishes at R.
f=lambda t:t*t-62*t+1
assert f(F(1,63))>0 and f(F(1,61))<0
print(json.dumps({'exact_tuple_kernel_cases':count,'channels':4,'n_max':7,'tuple_order_max':3,
 'inverse_filter_weights_lambda_1':[str(v) for v in weights],
 'renewal_thinning_coefficients_a_b_4_5_r_1_10':[str(v) for v in h[1:]],
 'discriminant_radius_interval':['1/63','1/61'],
 'meaning':'finite diagnostic only; no full reconstruction theorem or gate'},indent=2))
