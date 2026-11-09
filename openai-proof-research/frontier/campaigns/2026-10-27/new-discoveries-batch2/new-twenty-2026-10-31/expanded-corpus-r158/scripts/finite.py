import itertools as I,json,sys,math
mode=sys.argv[1]
def connected(n,es):
 seen={0};q=[0]
 for u in q:
  for a,b in es:
   v=b if a==u else a if b==u else -1
   if v>=0 and v not in seen:seen.add(v);q.append(v)
 return len(seen)==n
if mode=='majority':
 for n in range(1,5):
  arcs=[(u,v) for u in range(n) for v in range(n) if u!=v];cnt=0
  for mask in range(1<<len(arcs)):
   out=[[] for _ in range(n)]
   for i,(u,v) in enumerate(arcs):
    if mask>>i&1:out[u].append(v)
   ok=any(all(2*sum(c[v]==c[u] for v in out[u])<=len(out[u]) for u in range(n)) for c in I.product(range(3),repeat=n))
   assert ok;cnt+=1
  print(json.dumps(dict(mode=mode,n=n,digraphs=cnt,failures=0)),flush=True)
if mode=='liking':
 for n in range(5,8):
  opts=[[mask for mask in range(1<<n) if not mask>>u&1 and mask.bit_count()>=4] for u in range(n)]
  rows=[];sol=[];nodes=0
  def rec(u):
   global nodes
   nodes+=1
   if u==n:sol.append(rows[:]);return
   for r in opts[u]:
    if any((r&s).bit_count()<3 for s in rows):continue
    if any((r&rows[i]&rows[j]).bit_count()!=2 for i,j in I.combinations(range(u),2)):continue
    rows.append(r);rec(u+1);rows.pop()
  rec(0)
  print(json.dumps(dict(mode=mode,t=3,lam=2,n=n,row_options=[len(o) for o in opts],nodes=nodes,solutions=len(sol),rows=sol[:3])),flush=True)
if mode=='product':
 for n in range(2,6):
  allE=list(I.combinations(range(n),2));cnt=0;unknown=0;attempts=0
  for mask in range(1<<len(allE)):
   es=[e for i,e in enumerate(allE) if mask>>i&1];m=len(es)
   if m<3 or not connected(n,es):continue
   cnt+=1;ok=False
   for c in I.islice(I.permutations(range(1,m+1)),10000):
    attempts+=1;p=[1]*n
    for (u,v),a in zip(es,c):p[u]*=a;p[v]*=a
    if len(set(p))==n:ok=True;break
   if not ok:unknown+=1
  print(json.dumps(dict(mode=mode,n=n,graphs=cnt,permutations_tried=attempts,unresolved_at_10000=unknown)),flush=True)
if mode=='evenholes':
 for n in range(1,7):
  allE=list(I.combinations(range(n),2));qual=0
  for mask in range(1<<len(allE)):
   adj=[0]*n
   for i,(u,v) in enumerate(allE):
    if mask>>i&1:adj[u]|=1<<v;adj[v]|=1<<u
   if any((adj[u]&adj[v]) for u,v in allE if adj[u]>>v&1):continue
   # n<=6: triangle-free graph lies in H2 iff contains C4 and no induced C6;
   # H3 adds the induced 6-cycle cases with no C4.
   c4=any(all((adj[u]&s).bit_count()==2 for u in range(n) if s>>u&1)
          for s in range(1<<n) if s.bit_count()==4)
   if not c4:continue # test only H2 here
   if n==6 and all(a.bit_count()==2 for a in adj) and connected(n,[(u,v) for u,v in allE if adj[u]>>v&1]):continue
   qual+=1
   assert any(all(c[u]!=c[v] for u,v in allE if adj[u]>>v&1) for c in I.product(range(3),repeat=n))
  print(json.dumps(dict(mode=mode,n=n,H2_graphs=qual,failures=0)),flush=True)
