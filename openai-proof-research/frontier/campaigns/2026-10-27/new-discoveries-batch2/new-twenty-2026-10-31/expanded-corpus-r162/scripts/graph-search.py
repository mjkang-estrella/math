import pathlib,json,itertools,functools,time
D=pathlib.Path(__file__).resolve().parents[1];start=time.monotonic();out=[]
def contains(a,t):
 n=len(a);m=len(t);order=sorted(range(m),key=lambda v:-len(t[v]));mp={}
 def go(j,used):
  if j==m:return True
  v=order[j]
  for w in range(n):
   if used>>w&1 or a[w].bit_count()<len(t[v]):continue
   if any(not(a[w]>>mp[u]&1) for u in t[v] if u in mp):continue
   mp[v]=w
   if go(j+1,used|1<<w):return True
   del mp[v]
  return False
 return go(0,0)
def canon(a,v,p=-1):return '('+''.join(sorted(canon(a,u,v) for u in a[v] if u!=p))+')'
trees={}
for m in range(2,7):
 seen={}
 for code in itertools.product(range(m),repeat=m-2):
  deg=[1+code.count(i) for i in range(m)];a=[set() for _ in range(m)]
  for x in code:
   y=next(i for i in range(m) if deg[i]==1);a[x].add(y);a[y].add(x);deg[x]-=1;deg[y]-=1
  x,y=[i for i in range(m) if deg[i]==1];a[x].add(y);a[y].add(x)
  key=min(canon(a,v) for v in range(m));seen[key]=a
 trees[m]=list(seen.values())
for n in range(2,7):
 pairs=list(itertools.combinations(range(n),2));total=1<<len(pairs);tests=0;counter=None;dyn=0
 for mask in range(total):
  a=[0]*n
  for j,(u,v) in enumerate(pairs):
   if mask>>j&1:a[u]|=1<<v;a[v]|=1<<u
  deg=[x.bit_count() for x in a]
  for k in range(1,n):
   threshold=n/2-n//(k+1)-n%(k+1)
   if sum(d>=k for d in deg)<=threshold:continue
   for t in trees[k+1]:
    tests+=1
    if not contains(a,t):
     counter={'n':n,'k':k,'mask':mask,'tree':[sorted(z) for z in t]};break
   if counter:break
  if counter:break
  if n==6:
   # K5 minor by deleting a vertex or contracting an edge; K3,3 minor is subgraph at order 6.
   nonplanar=any(all(a[u]>>v&1 for u,v in itertools.combinations(vs,2)) for vs in itertools.combinations(range(n),5))
   if not nonplanar:
    for u,v in pairs:
     if not a[u]>>v&1:continue
     others=[x for x in range(n) if x not in [u,v]]
     if all(a[x]>>y&1 for x,y in itertools.combinations(others,2)) and all((a[u]|a[v])>>x&1 for x in others):nonplanar=True;break
   if not nonplanar:
    for s in itertools.combinations(range(n),3):
     if all(a[u]>>v&1 for u in s for v in range(n) if v not in s):nonplanar=True;break
   if not nonplanar:
    dyn+=1
    # 5-coloring on six vertices can be obtained by identifying one nonedge.
    ok=False
    for u,v in pairs:
     if a[u]>>v&1:continue
     f=list(range(n));f[v]=u
     if all(len({f[w] for w in range(n) if a[x]>>w&1})>=min(2,deg[x]) for x in range(n)):ok=True;break
    if not ok:raise Exception(('dynamic_counterexample',mask))
 row={'n':n,'graphs_completed':mask+1,'graphs_total':total,'sharp_tree_tests':tests,'tree_types':{k:len(v) for k,v in trees.items() if k<=n},'counterexample':counter,'planar_dynamic_r2_tested':dyn}
 out.append(row);(D/'outputs/graph-search.json').write_text(json.dumps(out,indent=2));print(row,flush=True)
 if counter:break
print('wall',time.monotonic()-start)
