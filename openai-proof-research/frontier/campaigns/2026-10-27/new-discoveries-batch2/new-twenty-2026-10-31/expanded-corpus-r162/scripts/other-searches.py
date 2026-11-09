import pathlib,json,itertools,random,functools,time
D=pathlib.Path(__file__).resolve().parents[1];out={}
# All oriented loopless graphs on four labeled vertices, no hypothesis overclaim.
n=4;pairs=list(itertools.combinations(range(n),2));cyclic=0;failed=[]
for code in itertools.product(range(3),repeat=6):
 a=[set() for _ in range(n)]
 for c,(u,v) in zip(code,pairs):
  if c==1:a[u].add(v)
  if c==2:a[v].add(u)
 cycles=set()
 for k in range(3,n+1):
  for p in itertools.permutations(range(n),k):
   if all(p[(j+1)%k] in a[p[j]] for j in range(k)):cycles.add(frozenset(p))
 if not cycles:continue
 cyclic+=1;g=min(map(len,cycles))
 if not any(all(len({col[v] for v in C})==g for C in cycles) for col in itertools.product(range(g),repeat=n)):
  failed.append(code)
out['342051']={'n':4,'oriented_graphs':729,'cyclic_graphs':cyclic,'failed_polychromatic_cycle_test':failed,'limitation':'No digons; no larger-order coverage; four-vertex graph embedding is planar and all vertex degrees at most 3.'}
# All simple cubic graphs on four/six labels, exact proper 3-edge-color search.
res=[]
for n in [4,6]:
 pairs=list(itertools.combinations(range(n),2));count=0;fails=[]
 for es in itertools.combinations(pairs,3*n//2):
  deg=[0]*n
  for u,v in es:deg[u]+=1;deg[v]+=1
  if deg!=[3]*n:continue
  count+=1;used=[0]*n
  def dfs(j):
   if j==len(es):return True
   u,v=es[j]
   for c in [1,2,4]:
    if (used[u]|used[v])&c:continue
    used[u]|=c;used[v]|=c
    if dfs(j+1):return True
    used[u]^=c;used[v]^=c
   return False
  if not dfs(0):fails.append(es)
 res.append({'n':n,'cubic_graphs':count,'without_3_edge_coloring':fails})
out['342134']=res
# First unproved r=5; structured complete-graph colorings via affine-coordinate words.
rng=random.Random(162);res=[]
def cover(sets,N,k):
 full=(1<<N)-1;sets=list(set(sets))
 @functools.lru_cache(None)
 def go(covered,left):
  if covered==full:return True
  if not left:return False
  missing=full^covered;v=(missing&-missing).bit_length()-1
  return any(go(covered|s,left-1) for s in sets if s>>v&1)
 return go(0,k)
for N in [6,10,15,20]:
 fails=0
 for case in range(200):
  col={(i,j):rng.randrange(5) for i in range(N) for j in range(i+1,N)}
  comps=[[] for _ in range(5)]
  for c in range(5):
   rem=set(range(N))
   while rem:
    v=rem.pop();vs={v};todo=[v]
    for x in todo:
     for y in list(rem):
      if col[min(x,y),max(x,y)]==c:rem.remove(y);vs.add(y);todo.append(y)
    comps[c].append(sum(1<<v for v in vs))
  for S in [{0,1},{0},{0,1,2}]:
   if not (cover([z for c in S for z in comps[c]],N,4) or cover([z for c in range(5) if c not in S for z in comps[c]],N,4)):fails+=1
 res.append({'n':N,'random_5_colorings':200,'S_sets':[[0],[0,1],[0,1,2]],'failures':fails})
out['347959']=res
(D/'outputs/other-searches.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
