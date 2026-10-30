from fractions import Fraction as F
from itertools import product
import random,json
def prox(a,t):
 n=len(a);order=sorted(range(n),key=lambda i:a[i]);blocks=[]
 for j,i in enumerate(order):
  blocks.append(([i],a[i]-t*(2*j-n+1)))
  while len(blocks)>1 and blocks[-2][1]/len(blocks[-2][0])>blocks[-1][1]/len(blocks[-1][0]):
   y,v=blocks.pop();x,u=blocks.pop();blocks.append((x+y,u+v))
 out=[F(0)]*n
 for inds,total in blocks:
  for i in inds:out[i]=total/len(inds)
 return out
def directional(a,t,u,w):
 z=sum((u[i]-a[i])*w[i] for i in range(len(a)))
 for i in range(len(a)):
  for j in range(i):
   d=u[i]-u[j];v=w[i]-w[j];z+=t*(abs(v) if not d else (1 if d>0 else -1)*v)
 return z
def haus(a,b):return max(max(min(abs(x-y) for y in b) for x in a),max(min(abs(x-y) for y in a) for x in b))
rng=random.Random(192);cases=dirs=0
for n in range(2,11):
 for z in range(60):
  a=[F(rng.randrange(-20,21),3) for _ in range(n)];b=[x+F(rng.randrange(-2,3),7) for x in a]
  t=F(rng.randrange(0,8),5);s=F(rng.randrange(0,8),5);u=prox(a,t);v=prox(b,s)
  assert max(abs(u[i]-v[i]) for i in range(n))<=max(abs(a[i]-b[i]) for i in range(n))+(n-1)*abs(t-s)
  assert max(abs(u[i]-a[i]) for i in range(n))<=(n-1)*t
  for i in range(n):
   for j in range(i):
    if abs(a[i]-a[j])<=2*t:assert u[i]==u[j]
  if n<=5 and z<8:
   for w in product([-1,0,1],repeat=n):assert directional(a,t,u,w)>=0;dirs+=1
  cases+=1
x=[[F(0),F(0),F(0)],[F(2),F(0),F(-2)],[F(0),F(4),F(-4)]]
cols=[prox([p[j] for p in x],F(1)) for j in range(3)]
ys=list(zip(*cols));sums=[sum(p) for p in ys];assert sums==[F(-1,3),F(-1,3),F(2,3)]
hard=[]
for q in [10,100,1000,10000]:
 e=F(1,q);a=[F(1),4+e];b=[F(0),3-e/2];ratio=haus(a,b)/(2*e);assert ratio>=q/2
 hard.append(dict(epsilon=str(e),output_distance=str(haus(a,b)),input_distance=str(2*e),ratio=str(ratio)))
print(json.dumps(dict(seed=192,prox_pairs=cases,directional_checks=dirs,subspace_output=[[str(v) for v in p] for p in ys],subspace_sums=list(map(str,sums)),hard_pair_instability=hard,scope='Exact finite diagnostics; not an all-space/all-order source proof.'),indent=2))
