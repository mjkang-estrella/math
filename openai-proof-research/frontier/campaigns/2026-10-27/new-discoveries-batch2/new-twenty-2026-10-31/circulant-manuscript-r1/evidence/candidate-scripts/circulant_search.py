import itertools,json,pathlib,sys,time
D=pathlib.Path(__file__).resolve().parents[1]
def canon(t,n):return min(tuple(sorted((x-a)%n for x in t)) for a in t)
def check(n,S,cap=200000):
 adj=[sum(1<<((i+s)%n) for s in S) for i in range(n)]
 if any(adj[0]&adj[s] for s in S):return {'triangle':True}
 if ((adj[0]|sum([],[])) if False else 0):pass
 reach=adj[0]|1
 for s in S:reach|=adj[s]
 if reach!=(1<<n)-1:return {'diameter_gt2':True}
 missing={canon((0,a,b),n) for a in range(1,n) for b in range(a+1,n)};nodes=0;witness={}
 def dfs(path,used,forbid):
  nonlocal nodes
  nodes+=1
  if nodes>cap:return False
  v=path[-1]
  for a,b in itertools.combinations(path[:-1],2):
   key=canon((a,b,v),n)
   if key in missing:missing.remove(key);witness[str(key)]=path[:]
  if not missing:return True
  opts=adj[v]&~(used|forbid)
  while opts:
   bit=opts&-opts;opts-=bit;w=bit.bit_length()-1
   if dfs(path+[w],used|bit,forbid|adj[v]):return True
   if nodes>cap:return False
  return False
 dfs([0],1,0)
 return dict(success=not missing,nodes=nodes,uncovered_orbits=len(missing),first_uncovered=sorted(missing)[:3],witnesses=witness)

if __name__=='__main__':
 import random
 rng=random.Random(108);res=[]
 for n in range(11,int(sys.argv[1])+1):
  trials=0; success=None; diagnostics={}
  candidates=itertools.chain(itertools.combinations(range(1,n//2+1),2),itertools.combinations(range(1,n//2+1),3),(rng.sample(range(1,n//2+1),rng.randrange(2,max(3,n//5))) for _ in range(300)))
  for positive in candidates:
   S=sorted(set(positive)|{n-x for x in positive});trials+=1
   r=check(n,S,5000)
   label='success' if r.get('success') else ('triangle' if r.get('triangle') else ('diameter_gt2' if r.get('diameter_gt2') else 'path_failure_or_cap'))
   diagnostics[label]=diagnostics.get(label,0)+1
   if r.get('success'):success=dict(S=S,**r);break
  row=dict(n=n,trials=trials,diagnostics=diagnostics,success=success);res.append(row);print(n,trials,positive if success else None,diagnostics,flush=True)
  (D/'outputs/circulant-search.json').write_text(json.dumps(res,indent=2))
