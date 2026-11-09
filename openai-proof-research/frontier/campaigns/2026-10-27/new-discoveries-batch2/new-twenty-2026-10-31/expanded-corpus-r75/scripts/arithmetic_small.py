import itertools as it,math,json,pathlib,collections
from fractions import Fraction as F
D=pathlib.Path(__file__).resolve().parents[1];out={}
# All source reduced fractions for each dyadic shell Q<q<=2Q; strict circular radius Q^-3.
a=[]
for Q in range(1,25):
 S=sorted(F(x,q*q) for q in range(Q+1,2*Q+1) for x in range(1,q*q) if math.gcd(x,q)==1);N=len(S);T=[x-1 for x in S]+S+[x+1 for x in S];r=F(1,Q**3);lo=hi=0;mx=0
 for x in S:
  while lo<len(T) and T[lo]<=x-r:lo+=1
  while hi<len(T) and T[hi]<x+r:hi+=1
  mx=max(mx,hi-lo)
 # Three-copy method overcounts the identical point when radius>=1/2; correct the tiny Q by direct unique counting.
 if Q==1:mx=N
 a.append({'Q':Q,'fractions':N,'max_local_count':mx})
out['379188']=a;(D/'outputs/arithmetic-small.json').write_text(json.dumps(out,indent=2))
# Exact determinant and nearest singular matrix in the entire Bernoulli Hamming cube.
a=[]
for n in range(1,5):
 perms=list(it.permutations(range(n)));terms=[([i*n+p[i] for i in range(n)],(-1)**sum(p[i]>p[j] for i in range(n) for j in range(i+1,n))) for p in perms];N=1<<(n*n);dist=[-1]*N;q=collections.deque()
 for mask in range(N):
  det=sum(sg*((-1)**sum(mask>>z&1 for z in idx)) for idx,sg in terms)
  if det==0:dist[mask]=0;q.append(mask)
 while q:
  m=q.popleft()
  for z in range(n*n):
   k=m^(1<<z)
   if dist[k]<0:dist[k]=dist[m]+1;q.append(k)
 a.append({'n':n,'all_matrices':N,'resilience_histogram':dict(collections.Counter(dist)),'note':'n=1 has no singular +/-1 matrix; distance -1 means no target'})
out['380168']=a;(D/'outputs/arithmetic-small.json').write_text(json.dumps(out,indent=2));print(out)
