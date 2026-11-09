import random,itertools,json,hashlib,time
from functools import lru_cache
random.seed(352123)
@lru_cache(None)
def covers(p):
 out=[]
 for i in range(len(p)):
  for j in range(i+1,len(p)):
   if p[i]>p[j] and not any(p[j]<p[k]<p[i] for k in range(i+1,j)):
    a=list(p);a[i],a[j]=a[j],a[i];out.append(tuple(a))
 return tuple(out)
def leq(u,v):return all(sum(x>=k for x in u[:i])<=sum(x>=k for x in v[:i]) for i in range(1,len(u)+1) for k in range(len(u)))
def interval(u,v):
 seen={v};todo=[v];edges=[]
 while todo:
  a=todo.pop()
  for b in covers(a):
   if not leq(u,b):continue
   edges.append((a,b))
   if b not in seen:seen.add(b);todo.append(b)
 return seen,edges
def fingerprint(nodes,edges):
 adj={v:[] for v in nodes}
 for a,b in edges:
  if a in nodes and b in nodes:adj[a].append(b)
 cache={}
 def f(v):
  if v not in cache:cache[v]=hashlib.sha256(str(sorted(f(x) for x in adj[v])).encode()).hexdigest()
  return cache[v]
 # rank-profile and recursive lower-cover hash only, not a canonical poset form
 return sorted(f(v) for v in nodes)
seen={};rows=[];leads=[]
for it in range(400):
 v=list(range(8));random.shuffle(v);v=tuple(v);u=v
 steps=random.choice([4,5,6])
 for j in range(steps):
  cs=covers(u)
  if not cs:break
  u=random.choice(cs)
 nodes,edges=interval(u,v)
 deck=[]
 for c in covers(v):
  if c in nodes:
   ns,es=interval(u,c);deck.append(fingerprint(ns,es))
 key=hashlib.sha256(str(sorted(deck)).encode()).hexdigest();fp=fingerprint(nodes,edges)
 if key in seen and seen[key]['fingerprint']!=fp:leads.append(dict(u=u,v=v,previous=seen[key]))
 seen[key]=dict(u=u,v=v,fingerprint=fp)
 rows.append(dict(u=u,v=v,size=len(nodes),coatom_count=len(deck),deck_fingerprint=key))
json.dump(dict(scope='400 sampled intervals in S8 (type A7); rank difference 4 to 6 unless chain ends; recursive lower-cover fingerprints are diagnostics, not certified isomorphism classes',rows=rows,invariant_mismatch_leads=leads),open('outputs/bruhat.json','w'),indent=2)
print('intervals',len(rows),'distinct deck fingerprints',len(seen),'leads',len(leads),'maximum size',max(x['size'] for x in rows),flush=True)
