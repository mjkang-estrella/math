from pathlib import Path
from fractions import Fraction as Q
from itertools import product
from collections import Counter
import json
L=Path(__file__).parent
def subsums(xs):
 c=Counter({Q(0):1})
 for x in xs:
  d=Counter(c)
  for s,n in c.items():d[s+x]+=n
  c=d
 return c
# Prefix partition identity on exact finite models with repeats and carries.
models=[[Q(1,2),Q(1,4),Q(1,4),Q(1,8)],[Q(1,3)]*4,[Q(1,5),Q(2,5),Q(3,5),Q(1,25)]]
cases=0
for xs in models:
 for k in range(len(xs)+1):
  total=subsums(xs);left=subsums(xs[:k]);right=subsums(xs[k:]);calc=Counter()
  for a,m in left.items():
   for b,n in right.items():calc[a+b]+=m*n
  assert calc==total;cases+=1
# n-clopen-piece Cantor map: finite binary codes partition suffixes.
for n in range(1,13):
 prefixes=[''] if n==1 else ['0'*j+'1' for j in range(n-1)]+['0'*(n-1)]
 assert len(prefixes)==n
 for bits in product('01',repeat=n+2):
  s=''.join(bits);assert sum(s.startswith(p) for p in prefixes)==1
 assert 3*Q(1,4)**(n+1)<2*Q(1,4)**n
# Dyadic infinite-tail identity and forced endpoint pattern for its finite truncation.
for k in range(1,20):
 for m in [k+1,k+3,k+8]:
  assert sum((Q(1,2)**i for i in range(k+1,m+1)),Q(0))+Q(1,2)**m==Q(1,2)**k
  c=subsums([Q(1,2)**i for i in range(k,m+1)]+[Q(1,2)**m])
  assert max(c.values())==2
# Separated duplicate pairs still have exponentially many choices.
for k in range(1,9):
 c=subsums([Q(1,4)**j for j in range(1,k+1) for _ in range(2)])
 t=sum((Q(1,4)**j for j in range(1,k+1)),Q(0))
 assert c[t]==2**k
out={'status':'PASS','prefix_identity_models':cases,'cantor_partition_n_max':12,'dyadic_relation_controls':57,'independent_block_k_max':8,'scope':'exact finite controls only; no infinite source theorem tested or claimed'}
(L/'checks-result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
