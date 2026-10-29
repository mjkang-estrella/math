import functools,json,time
from pathlib import Path

def calc(par,ds):
 n=len(par)-1;child=[0]*(n+1);anc=[0]*(n+1)
 for v in range(1,n+1):
  child[par[v]]|=1<<(v-1);p=par[v]
  while p:anc[v]|=1<<(p-1);p=par[p]
 order=[]
 def dfs(v):
  for w in range(1,n+1):
   if par[w]==v:dfs(w)
  if v:order.append(v)
 dfs(0);rank={v:i for i,v in enumerate(order)}
 right=[sum(1<<(w-1) for w in range(1,n+1) if rank[w]>rank[v] and not (anc[w]>>(v-1)&1) and not (anc[v]>>(w-1)&1)) for v in range(1,n+1)]
 @functools.lru_cache(None)
 def rec(mask):
  if not mask:return (1,)
  t=n-mask.bit_count()+1;out=[0];avail=mask
  while avail:
   bit=avail&-avail;avail-=bit;v=bit.bit_length()
   if child[v]&mask or ds.get(v,1)>t:continue
   q=rec(mask^bit);shift=(mask&right[v-1]).bit_count()
   if len(out)<len(q)+shift:out.extend([0]*(len(q)+shift-len(out)))
   for i,x in enumerate(q):out[i+shift]+=x
  while len(out)>1 and out[-1]==0:out.pop()
  return tuple(out)
 q=rec((1<<n)-1);states=rec.cache_info().currsize;rec.cache_clear();return q,states

def uni(q):
 falling=False
 for a,b in zip(q,q[1:]):
  if b<a:falling=True
  if falling and b>a:return False
 return True

def build(branches):
 p=[-1]
 def put(shape,parent):
  v=len(p);p.append(parent)
  for x in shape:put(x,v)
 for x in branches:put(x,0)
 leaves=[v for v in range(1,len(p)) if v not in p]
 return p,leaves

def chain(n):
 s=()
 for _ in range(n-1):s=(s,)
 return s

def fork(stem,a,b):
 s=(chain(a),chain(b))
 for _ in range(stem-1):s=(s,)
 return s

def run():
 shapes=[]
 for a,b,c in [(1,1,1),(1,1,3),(1,2,4),(2,1,4),(3,1,2),(1,3,2),(4,1,1),(2,2,2)]:
  shapes.extend([('path-fork',[chain(a),fork(1,b,c)]),('fork-path',[fork(1,b,c),chain(a)])])
 for a,b,c,d in [(1,1,1,1),(1,1,1,3),(1,2,1,3),(1,3,3,1),(1,1,2,4),(2,1,3,1),(2,2,1,2),(1,1,1,5)]:
  shapes.append(('two-forks',[fork(1,a,b),fork(1,c,d)]))
 for a,b,c in [(1,1,2),(1,2,3),(2,1,3),(3,1,1),(1,1,5),(2,2,2)]:
  shapes.extend([('three-branches',[chain(a),fork(1,b,c),chain(1)]),('nested-comb',[(chain(a),fork(1,b,c)),chain(1)])])
 records=[];start=time.monotonic()
 for name,shape in shapes:
  p,ls=build(shape);n=len(p)-1;k=len(ls);dsset=set()
  for pivot in range(k):
   for left in sorted({1,2,3,n//2,n-2,n-1}):
    for right in sorted({1,2,3,n//2,n-2,n-1}):
     dsset.add(tuple(left if i<pivot else 1 if i==pivot else right for i in range(k)))
  for ds in sorted(dsset):
   q,states=calc(p,dict(zip(ls,ds)));r=dict(family=name,parents=p,leaves=ls,delays=ds,Q=q,states=states,unimodal=uni(q));records.append(r)
   if not r['unimodal']:
    Path('candidate.json').write_text(json.dumps(r,indent=2));Path('structured-checks.json').write_text(json.dumps(records,indent=2));print('FOUND',json.dumps(r));return
 Path('structured-checks.json').write_text(json.dumps(records,indent=2));print(json.dumps(dict(cases=len(records),shapes=len(shapes),seconds=time.monotonic()-start,nonunimodal=0,max_edges=max(len(x['parents'])-1 for x in records))))
if __name__=='__main__':run()
