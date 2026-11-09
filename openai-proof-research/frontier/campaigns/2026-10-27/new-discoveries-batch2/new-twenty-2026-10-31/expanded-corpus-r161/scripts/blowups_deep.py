import itertools,math,pathlib,json,sys,collections,fractions,time
D=pathlib.Path(__file__).resolve().parents[1];mode=sys.argv[1];out=[]
def distances(adj):
 ds=[]
 for s in range(len(adj)):
  d=[99]*len(adj);d[s]=0;q=[s]
  for v in q:
   for w in adj[v]:
    if d[w]==99:d[w]=d[v]+1;q.append(w)
  ds.append(d)
 return ds
if mode=='trees':
 trees=[((),)];total=0
 def canon(adj):
  def rooted(v,p):return '('+''.join(sorted(rooted(w,v) for w in adj[v] if w!=p))+')'
  return min(rooted(v,-1) for v in range(len(adj)))
 for n in range(1,15):
  failures=[];tested=0;maxnodes=0
  for adj in trees:
   ds=distances(adj);k=math.isqrt(n-1)+1;full=(1<<n)-1
   balls=[[sum(1<<w for w in range(n) if ds[v][w]<=r) for v in range(n)] for r in range(k)]
   memo=set();nodes=[0]
   def burn(r,mask):
    nodes[0]+=1
    if mask==full:return True
    if r<0:return False
    if (r,mask) in memo:return False
    memo.add((r,mask))
    for b in sorted(set(balls[r]),key=lambda b:(b&~mask).bit_count(),reverse=True):
     if burn(r-1,mask|b):return True
    return False
   ok=burn(k-1,0);tested+=1;maxnodes=max(maxnodes,nodes[0])
   if not ok:failures.append(adj)
  out.append({'n':n,'unlabeled_trees_tested':tested,'failures':failures,'max_backtrack_nodes':maxnodes});print(out[-1],flush=True)
  if n==14:break
  nxt={}
  for adj in trees:
   for v in range(n):
    a=[list(x) for x in adj]+[[v]];a[v].append(n);key=canon(a);nxt[key]=tuple(tuple(x) for x in a)
  trees=list(nxt.values())
if mode=='blowups':
 def centrality(adj):
  n=len(adj);cb=[fractions.Fraction(0) for _ in adj]
  for s in range(n):
   stack=[];pred=[[] for _ in adj];sig=[0]*n;sig[s]=1;dist=[-1]*n;dist[s]=0;q=collections.deque([s])
   while q:
    v=q.popleft();stack.append(v)
    for w in adj[v]:
     if dist[w]<0:dist[w]=dist[v]+1;q.append(w)
     if dist[w]==dist[v]+1:sig[w]+=sig[v];pred[w].append(v)
   delta=[fractions.Fraction(0) for _ in adj]
   for w in reversed(stack):
    for v in pred[w]:delta[v]+=fractions.Fraction(sig[v],sig[w])*(1+delta[w])
    if w!=s:cb[w]+=delta[w]
  return cb
 for n in range(4,7):
  es=list(itertools.combinations(range(n),2));seen=set();bases=checks=0;witness=[]
  for mask in range(1<<len(es)):
   adj=[[] for _ in range(n)]
   for i,(v,w) in enumerate(es):
    if mask>>i&1:adj[v].append(w);adj[w].append(v)
   ds=distances(adj)
   if max(ds[0])==99 or max(map(max,ds))<3:continue
   cuts=[]
   for c in range(n):
    reached={next(v for v in range(n) if v!=c)};todo=list(reached)
    for v in todo:
     for w in adj[v]:
      if w!=c and w not in reached:reached.add(w);todo.append(w)
    if len(reached)<n-1:cuts.append(c)
   if not cuts:continue
   codes=[]
   for perm in itertools.permutations(range(n)):
    codes.append(tuple(int(perm[w] in adj[perm[v]]) for v,w in es))
   key=min(codes)
   if key in seen:continue
   seen.add(key);bases+=1
   # module type 0 singleton, 1 independent2, 2 clique2, 3 independent3, 4 clique3
   for types in itertools.product(range(5 if n<6 else 3),repeat=n):
    modules=[];j=0
    for t in types:
     size=1 if t==0 else 2 if t<=2 else 3;modules.append(list(range(j,j+size)));j+=size
    a=[set() for _ in range(j)]
    for v in range(n):
     if types[v] in [2,4]:
      for x,y in itertools.combinations(modules[v],2):a[x].add(y);a[y].add(x)
     for w in adj[v]:
      for x in modules[v]:a[x].update(modules[w])
    cb=centrality(a);checks+=1
    if len(set(cb))==1:witness.append({'base':adj,'types':types,'betweenness_twice':str(cb[0])})
   print({'base_n':n,'bases_done':bases,'checks':checks,'witness_count':len(witness)},flush=True)
  out.append({'base_n':n,'nonisomorphic_eligible_bases':bases,'blowups_tested':checks,'witnesses':witness})
(D/f'outputs/{mode}.json').write_text(json.dumps(out,indent=2)+'\n')
