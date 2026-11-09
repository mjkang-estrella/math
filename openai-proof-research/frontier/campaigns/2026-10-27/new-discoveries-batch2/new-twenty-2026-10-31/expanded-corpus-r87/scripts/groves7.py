import itertools as it,json,time,random
from functools import lru_cache
@lru_cache(None)
def trees(mask):
 if mask.bit_count()==1:return (mask.bit_length()-1,)
 low=mask&-mask;out=[];sub=(mask-1)&mask
 while sub:
  other=mask^sub
  if other and sub&low:
   out += [(a,b) for a in trees(sub) for b in trees(other)]
  sub=(sub-1)&mask
 return tuple(out)
def restrict(t,mask):
 if isinstance(t,int):return t if mask>>t&1 else None
 a,b=(restrict(x,mask) for x in t)
 if a is None:return b
 if b is None:return a
 return tuple(sorted((a,b),key=repr))
@lru_cache(None)
def partitions(t):
 if not t:return ((),)
 x,*tail=t;out=[]
 for p in partitions(tuple(tail)):
  out.append(((x,),)+p)
  for j,b in enumerate(p):out.append(p[:j]+((x,)+b,)+p[j+1:])
 return tuple(out)

from pathlib import Path
D=Path(__file__).resolve().parents[1]
n=7;full=(1<<n)-1;start=time.monotonic();ts=trees(full)
sets=[s for s in range(1,full+1) if s.bit_count() in [3,4]]
triples=[s for s in sets if s.bit_count()==3];allbits=(1<<len(ts))-1
projection={}
for s in sets:
 groups={}
 for j,t in enumerate(ts):
  key=repr(restrict(t,s));groups[key]=groups.get(key,0)|(1<<j)
 projection[s]=tuple(groups.values())
print(json.dumps(dict(stage='precompute',n=n,trees=len(ts),sets=len(sets),seconds=time.monotonic()-start)),flush=True)
@lru_cache(None)
def classify(family):
 groups=[allbits]
 for s in family:
  groups=[x&y for x in groups for y in projection[s] if x&y]
 resolved=0
 for q,t in enumerate(triples):
  if any(any(g&h==g for h in projection[t]) for g in groups):resolved|=1<<q
 strict=True
 for part in partitions(family):
  if len(part)<2:continue
  unions=[]
  for block in part:
   u=0
   for s in block:u|=s
   unions.append(u)
  U=0
  for u in unions:U|=u
  cross=sum(1<<q for q,t in enumerate(triples) if t&U==t and all(t&u!=t for u in unions))
  if not cross&resolved:strict=False
  if cross and not cross&resolved:return False,False
 return True,strict
mask=lambda c:sum(1<<(v-1) for v in c)
seed=tuple(sorted(mask(c) for c in [(2,3,6),(1,4,5),(2,4,5,7)]))
print(json.dumps(dict(stage='source-remark-3.19-check',family=seed,status=classify(seed),note='Adjacent source example only, not Conjecture 3.13 endpoint')),flush=True)
rng=random.Random(8704);strict=[];tested=0;filtered=0;deadline=time.monotonic()+45
while tested<3000 and time.monotonic()<deadline:
 fam=tuple(sorted(rng.sample(sets,rng.choice([2,3,4]))))
 private=True
 for s in fam:
  u=0
  for t in fam:
   if t!=s:u|=t
  if s&~u==0:private=False;break
 if not private:filtered+=1;continue
 tested+=1
 if classify(fam)[1] and fam not in strict:strict.append(fam)
print(json.dumps(dict(stage='strict-sampling',tested=tested,private_taxon_exclusions=filtered,strict=len(strict),seconds=time.monotonic()-start)),flush=True)
pairs=[(a,b) for j,a in enumerate(strict) for b in strict[j+1:] if set(a)&set(b)]
rng.shuffle(pairs);checked=0;bad=[]
for a,b in pairs:
 if checked>=1000 or time.monotonic()-start>100:break
 union=tuple(sorted(set(a)|set(b)));checked+=1
 if not classify(union)[0]:bad.append([a,b,union]);break
print(json.dumps(dict(stage='union-sampling',pairs_checked=checked,pairs_available=len(pairs),counterexamples=bad,seconds=time.monotonic()-start)),flush=True)
