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

rng=random.Random(8703)
n=6;full=(1<<n)-1;sets=[s for s in range(1,full+1) if s.bit_count() in [3,4]]
ts=trees(full);triples=[sum(1<<v for v in c) for c in it.combinations(range(n),3)]
restrictions=[[repr(restrict(t,s)) for s in sets] for t in ts]
tr=[[repr(restrict(t,s)) for s in triples] for t in ts]
@lru_cache(None)
def classify(family):
 groups={}
 for j,row in enumerate(restrictions):groups.setdefault(tuple(row[i] for i in family),[]).append(j)
 resolved=0
 for group in groups.values():
  for q in range(len(triples)):
   if all(tr[j][q]==tr[group[0]][q] for j in group):resolved|=1<<q
 strict=True
 for p in partitions(family):
  if len(p)<2:continue
  unions=[]
  for block in p:
   u=0
   for i in block:u|=sets[i]
   unions.append(u)
  union=0
  for u in unions:union|=u
  cross=sum(1<<q for q,t in enumerate(triples) if t&union==t and all(t&u!=t for u in unions))
  if not cross&resolved:strict=False
  if cross and not cross&resolved:return False,False
 return True,strict
strict=[];tested=0;filtered=0;start=time.monotonic()
for k in [2,3,4]:
 for family in it.combinations(range(len(sets)),k):
  private=True
  for i in family:
   others=0
   for j in family:
    if j!=i:others|=sets[j]
   if sets[i]&~others==0:private=False;break
  if not private:filtered+=1;continue
  tested+=1
  if classify(family)[1]:strict.append(family)
 print(json.dumps(dict(stage='strict-enumeration',n=n,max_family_size=k,classifications=tested,private_taxon_exclusions=filtered,strict=len(strict),seconds=time.monotonic()-start)),flush=True)
pairs=[(a,b) for j,a in enumerate(strict) for b in strict[j+1:] if set(a)&set(b)]
rng.shuffle(pairs);bad=[]
for a,b in pairs[:5000]:
 union=tuple(sorted(set(a)|set(b)))
 if not classify(union)[0]:bad.append([[sets[i] for i in a],[sets[i] for i in b]])
print(json.dumps(dict(stage='union-test',sampled_pairs=min(5000,len(pairs)),total_intersecting_strict_pairs=len(pairs),counterexamples=bad,seconds=time.monotonic()-start)),flush=True)
