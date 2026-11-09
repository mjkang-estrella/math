from itertools import permutations, combinations
from collections import Counter
from fractions import Fraction as Q
from pathlib import Path
import json
OUT=Path(__file__).parent

def cyc(w): return min(w[i:]+w[:i] for i in range(len(w)))
def F(bs):
 p=Counter()
 for s in permutations(range(4)):
  seen=set(); cs=[]
  for i in range(4):
   if i in seen: continue
   c=[];j=i
   while j not in seen:
    seen.add(j);c+=bs[j];j=s[j]
   cs.append(cyc(tuple(c)))
  p[tuple(sorted(cs))]+=(-1)**(4-len(cs))
 return {k:Q(v) for k,v in p.items() if v}
def add(a,b,c):
 for k,v in b.items():
  a[k]=a.get(k,Q(0))+c*v
  if not a[k]: del a[k]
from functools import lru_cache
TARGET=(3,2,2)
def deg(w):return tuple(w.count(i) for i in (1,2,3))
def sub(a,b):return tuple(x-y for x,y in zip(a,b))
@lru_cache(None)
def necklaces(d):
 if any(x<0 for x in d) or not sum(d):return ()
 return tuple(sorted({cyc(w) for w in set(permutations(tuple(i for i,n in zip((1,2,3),d) for _ in range(n))))}))
all_ds=[(a,b,c) for a in range(4) for b in range(3) for c in range(3)]
@lru_cache(None)
def trace_monomials(d,lo=()):
 if not sum(d):return ((),)
 out=[]
 for dd in all_ds:
  if not sum(dd) or any(x>y for x,y in zip(dd,d)):continue
  for w in necklaces(dd):
   if w<lo:continue
   for rest in trace_monomials(sub(d,dd),w):out.append((w,)+rest)
 return tuple(out)
lower_polynomials=[];witnesses=[]
for dd in all_ds:
 if not 4<=sum(dd)<=6:continue
 ws=set(permutations(tuple(i for i,n in zip((1,2,3),dd) for _ in range(n))))
 tuples=set()
 for w in ws:
  for cuts in combinations(range(1,len(w)),3):
   t=(0,)+cuts+(len(w),);tuples.add(tuple(sorted(w[t[i]:t[i+1]] for i in range(4))))
 for bs in sorted(tuples):
  f=F(bs)
  for m in trace_monomials(sub(TARGET,dd)):
   p={tuple(sorted(k+m)):v for k,v in f.items()};lower_polynomials.append(dict(p));witnesses.append({"blocks":[list(w) for w in bs],"multiplier":[list(w) for w in m]})

d=json.loads((OUT.parent/'hereditary-trace-fresh-r1/trace-exact-polynomials.json').read_text())
def read(xs):return {tuple(tuple(map(int,w)) for w in x['traces']):Q(x['coefficient']) for x in xs}
assert lower_polynomials==list(map(read,d['lower_identity_products']))
(OUT/'lower-witnesses.json').write_text(json.dumps(witnesses,indent=2))
print('PASS: all',len(witnesses),'lower products reconstructed as fundamental identity times trace monomial; no rank used; not Lean checked')
