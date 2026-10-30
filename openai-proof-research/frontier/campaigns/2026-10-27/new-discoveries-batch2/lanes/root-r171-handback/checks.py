import itertools,json,math
from pathlib import Path
import numpy as np
L=Path(__file__).resolve().parent
P=1000003

def rank(vectors):
 piv={}
 for v in vectors:
  v=np.array(v,dtype=np.int64)%P
  while np.any(v):
   k=int(np.flatnonzero(v)[0])
   if k not in piv:
    piv[k]=(v*pow(int(v[k]),-1,P))%P;break
   v=(v-int(v[k])*piv[k])%P
 return len(piv)
def words(n,d):
 return [w for j in range(d+1) for w in itertools.combinations_with_replacement(range(n),j)]
def mul(a,b):
 c={}
 for i,x in a.items():
  for j,y in b.items():
   if not i&j:c[i|j]=c.get(i|j,0)+x*y
 return {i:x for i,x in c.items() if x}
def gen(n,i):
 a=1<<i;b=1<<((i+1)%n);return {a:-1,b:1,a|b:-1}
def evaluated(n,ws):
 vals={():{0:1}}
 for w in ws:
  if w:vals[w]=mul(vals[w[:-1]],gen(n,w[-1]))
 return vals
def dense(v,N):
 a=[0]*N
 for i,x in v.items():a[i]=x
 return a
def predicted(n,d):
 ans=0
 for m in range(1<<n):
  if m.bit_count()>d or m&(((m<<1)|(m>>(n-1)))&((1<<n)-1)):continue
  c=sum(not(m>>i&1) and (m>>((i-1)%n)&1) and (m>>((i+1)%n)&1) for i in range(n))
  ans+=3**c
 return ans-(d>=2)
res=[]
for n,d in [(5,2),(7,3),(9,4)]:
 ws=words(n,d);ev=evaluated(n,ws);r=rank(dense(ev[w],1<<n) for w in ws)
 assert r==predicted(n,d)
 # Known exact source relations and all their degree-bounded multiples.
 rel=[]
 for w in words(n,d-2):
  a={}
  for i in range(n):
   for v,c in [(tuple(sorted(w+(i,))),2),(tuple(sorted(w+(i,i))),-1)]:a[v]=a.get(v,0)+c
  rel.append(a)
 if d>=3:
  for w in words(n,d-3):
   for i in range(n):
    rel.append({tuple(sorted(w+(i,i,i))):1})
    j=(i+1)%n
    rel.append({tuple(sorted(w+(i,i,j))):1,tuple(sorted(w+(i,j,j))):1})
 ix={w:i for i,w in enumerate(ws)}
 for a in rel:
  v={}
  for w,c in a.items():
   for k,x in ev[w].items():v[k]=v.get(k,0)+c*x
  assert all(x==0 for x in v.values())
 rr=rank(dense({ix[w]:c for w,c in a.items()},len(ws)) for a in rel)
 res.append(dict(n=n,d=d,word_columns=len(ws),ambient=1<<n,modular_evaluation_rank=r,conjectured_cumulative_rank=predicted(n,d),known_relation_rank=rr,additional_kernel_dimension_over_test_field=len(ws)-r-rr,qualification='finite modular diagnostic; no characteristic-zero upper rank certificate'))
# Multivariate Newton evaluation: Delta^a of q_S at 0 is its binomial-basis coefficient.
newton=0
for n,d in [(4,2),(5,2)]:
 for S in range(1<<n):
  def q(m):return math.prod(m[(i-1)%n]-m[i] for i in range(n) if S>>i&1)
  nodes=[]
  for w in words(n,d):
   a=tuple(w.count(i) for i in range(n));nodes.append(a)
  coeff={}
  for a in nodes:
   coeff[a]=sum((-1)**(sum(a)-sum(b))*math.prod(math.comb(x,y) for x,y in zip(a,b))*q(b) for b in itertools.product(*(range(x+1) for x in a)))
  for m in nodes:
   reconstructed=sum(c*math.prod(math.comb(x,y) if y<=x else 0 for x,y in zip(m,a)) for a,c in coeff.items())
   assert reconstructed==q(m);newton+=1
# Exact integer local quartic identities, candidates for a straightening scheme.
local=0
for n in range(5,13):
 for i in range(n):
  a,b,c=[gen(n,(i+j)%n) for j in range(3)]
  ac=mul(mul(a,a),mul(c,c))
  for v in [mul(mul(mul(a,a),b),c),mul(mul(a,b),mul(c,c))]:
   assert all(2*v.get(k,0)+ac.get(k,0)==0 for k in set(v)|set(ac));local+=1
out=dict(rank_diagnostics=res,newton_reconstruction_identities=newton,exact_local_quartic_identities=local,prime=P)
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
