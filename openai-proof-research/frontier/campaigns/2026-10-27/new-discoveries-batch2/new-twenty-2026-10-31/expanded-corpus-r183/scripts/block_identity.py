from pathlib import Path
from functools import lru_cache
from collections import Counter
from itertools import product
from math import comb
import json
D=Path(__file__).resolve().parents[1]
@lru_cache(None)
def weak(u,v):
 if not u:return {v:1}
 if not v:return {u:1}
 r=Counter()
 if u[0]<=v[0]:
  for w,c in weak(u[1:],v).items():r[u[:1]+w]+=c
 if v[0]<=u[0]:
  for w,c in weak(u,v[1:]).items():r[v[:1]+w]+=c
 return dict(r)
@lru_cache(None)
def shuffle(u,v):
 if not u:return {v:1}
 if not v:return {u:1}
 r=Counter()
 for w,c in shuffle(u[1:],v).items():r[u[:1]+w]+=c
 for w,c in shuffle(u,v[1:]).items():r[v[:1]+w]+=c
 return dict(r)
def split(w):
 chunks=w.split('b');return len(chunks[0]),tuple(len(s) for s in chunks[1:])
def combine(i,w):return 'a'*i+''.join('b'+'a'*j for j in w)
words=[''.join(w) for n in range(6) for w in product('ab',repeat=n)];pairs=0
for u in words:
 for v in words:
  i,U=split(u);j,V=split(v)
  expected={combine(i+j,w):comb(i+j,i)*c for w,c in shuffle(U,V).items()}
  assert weak(u,v)==expected,(u,v)
  pairs+=1
r={'word_lengths_each':[0,5],'ordered_pairs':pairs,'all_integer_structure_coefficients_match':True,'identity':'Phi(a^i ba^s1...ba^sk)=t^i/i! tensor [s1,...,sk]','status':'diagnostic; generic recursion proof recorded in CANDIDATE.md'}
(D/'outputs/block-identity.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
