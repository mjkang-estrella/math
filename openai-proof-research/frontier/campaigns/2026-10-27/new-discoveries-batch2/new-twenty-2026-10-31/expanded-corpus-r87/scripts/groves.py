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
for n,maxsize in [(4,11),(5,10),(6,4)]:
 start=time.monotonic();full=(1<<n)-1
 sets=[s for s in range(1,full+1) if (s.bit_count()>=2 if n==4 else s.bit_count()==3)]
 ts=trees(full);triples=[sum(1<<v for v in c) for c in it.combinations(range(n),3)]
 restrictions=[[repr(restrict(t,s)) for s in sets] for t in ts]
 tr=[[repr(restrict(t,s)) for s in triples] for t in ts]
 statuses={};strict=[];groves=0
 for k in range(2,min(maxsize,len(sets))+1):
  for family in it.combinations(range(len(sets)),k):
   groups={}
   for j,row in enumerate(restrictions):groups.setdefault(tuple(row[i] for i in family),[]).append(j)
   resolved=0
   for group in groups.values():
    for q in range(len(triples)):
     if all(tr[j][q]==tr[group[0]][q] for j in group):resolved|=1<<q
   grove=True;isstrict=True
   for p in partitions(family):
    if len(p)<2:continue
    unions=[0 for _ in p]
    for j,block in enumerate(p):
     for i in block:unions[j]|=sets[i]
    union=0
    for s in unions:union|=s
    cross=sum(1<<q for q,t in enumerate(triples) if t&union==t and all(t&u!=t for u in unions))
    informative=bool(cross&resolved)
    if not informative:isstrict=False
    if cross and not informative:grove=False;break
   statuses[family]=grove
   if grove:groves+=1
   if isstrict:strict.append(family)
 # Check unions known in table; larger union not enumerated is explicitly not tested.
 checked=0;bad=[];uncovered=0
 for j,a in enumerate(strict):
  for b in strict[j+1:]:
   if not set(a)&set(b):continue
   union=tuple(sorted(set(a)|set(b)))
   if union not in statuses:uncovered+=1;continue
   checked+=1
   if not statuses[union]:bad.append([a,b,union])
 print(json.dumps(dict(n=n,taxon_sets=sets,max_family_size=maxsize,global_binary_trees=len(ts),families=len(statuses),groves=groves,strict=len(strict),intersecting_strict_pairs_checked=checked,uncovered_union_pairs=uncovered,counterexamples=bad[:10],seconds=time.monotonic()-start)),flush=True)
