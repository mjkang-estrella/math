import pathlib,json,random,sys
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(164293)
def canon(adj):
 n=len(adj)
 def root(v,p):return '('+''.join(sorted(root(w,v) for w in adj[v] if w!=p))+')'
 deg=list(map(len,adj));leaves=[v for v in range(n) if deg[v]<=1];left=n
 while left>2:
  left-=len(leaves);new=[]
  for v in leaves:
   for w in adj[v]:
    deg[w]-=1
    if deg[w]==1:new.append(w)
  leaves=new
 return min(root(v,-1) for v in leaves)
def solve(adj):
 n=len(adj);B=2*n;root=max(range(n),key=lambda v:len(adj[v]));parent={root:-1};order=[root]
 for v in order:
  for w in sorted(adj[v],key=lambda x:-len(adj[x])):
   if w!=parent[v]:parent[w]=v;order.append(w)
 label=[0]*n;label[root]=1;label[order[1]]=2;used=(1<<1)|(1<<2)|(1<<3);nodes=0
 def go(j,used):
  nonlocal nodes
  nodes+=1
  if nodes>200000:return False
  if j==n:return True
  v=order[j];p=parent[v];a=label[p];cands=list(range(1,B));rng.shuffle(cands)
  for x in cands:
   y=x^a
   if not (used>>x&1 or used>>y&1):
    label[v]=x
    if go(j+1,used|(1<<x)|(1<<y)):return True
  return False
 ok=go(2,used)
 if ok:
  vals=label+[label[v]^label[w] for v in range(n) for w in adj[v] if v<w];assert sorted(vals)==list(range(1,B))
 return {'labels':label if ok else None,'nodes':nodes,'status':'witness' if ok else ('node_cap' if nodes>200000 else 'unsat')}
trees={'(())':[{1},{0}]};counts=[]
for n in range(2,19,2):
 if n in [2,4,8,16]:
  results=[]
  for key,adj in trees.items():
   s=solve(adj);results.append({'canonical':key,'edges':[(v,w) for v in range(n) for w in adj[v] if v<w],**s})
  (D/'outputs'/('trees-%d.json'%n)).write_text(json.dumps(results));print('TEST',n,len(results),{s:sum(x['status']==s for x in results) for s in ['witness','node_cap','unsat']},flush=True)
 counts.append([n,len(trees)]);(D/'outputs/tree-counts.json').write_text(json.dumps(counts))
 if n==18:break
 new={}
 for adj in trees.values():
  for v in range(n):
   a=[x.copy() for x in adj]+[{v},{v}];a[v]|={n,n+1};key=canon(a)
   if key not in new:new[key]=a
 trees=new;print('GEN',n+2,len(trees),flush=True)
