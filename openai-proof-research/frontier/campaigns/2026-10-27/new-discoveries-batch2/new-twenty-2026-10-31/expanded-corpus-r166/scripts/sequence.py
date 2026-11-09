import pathlib,json,itertools,random,time,sys
D=pathlib.Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r166');rng=random.Random(166);start=time.monotonic();stats=[]
def solve(n,edges,order,lists):
 rank={v:i for i,v in enumerate(order)};seq=[sorted([v]+[n+i for i,e in enumerate(edges) if v in e],key=rank.get) for v in range(n)]
 constraints=[list(zip(seq[u],seq[v])) for u,v in edges if len(seq[u])==len(seq[v])];assign=[None]*len(order)
 def go(t):
  if t==len(order):return True
  x=order[t]
  for value in lists[x]:
   assign[x]=value
   bad=False
   for c in constraints:
    if all(assign[a] is not None and assign[b] is not None and assign[a]==assign[b] for a,b in c):bad=True;break
   if not bad and go(t+1):return True
  assign[x]=None;return False
 return go(0)
mode=sys.argv[1]
if mode=='exhaustive':
 for n in range(1,4):
  E=list(itertools.combinations(range(n),2));count=0
  for mask in range(1<<len(E)):
   edges=[e for i,e in enumerate(E) if mask>>i&1];q=n+len(edges)
   for order in itertools.permutations(range(q)):
    for lists in itertools.product([(0,1),(0,2),(1,2)],repeat=q):
     count+=1
     if not solve(n,edges,order,lists):print('COUNTEREXAMPLE',n,edges,order,lists,flush=True);raise SystemExit(1)
  stats.append({'n':n,'cases':count});print(stats[-1],time.monotonic()-start,flush=True)
else:
 for n in range(4,7):
  E=list(itertools.combinations(range(n),2));count=graphs=0
  for mask in range(1<<len(E)):
   edges=[e for i,e in enumerate(E) if mask>>i&1];q=n+len(edges);graphs+=1
   for trial in range(8):
    order=list(range(q));rng.shuffle(order)
    lists=[(0,1) if trial==0 else rng.choice([(0,1),(0,2),(1,2)]) for _ in order];count+=1
    if not solve(n,edges,order,lists):print('COUNTEREXAMPLE',n,edges,order,lists,flush=True);raise SystemExit(1)
  stats.append({'n':n,'graphs':graphs,'cases':count,'trials_per_graph':8});print(stats[-1],time.monotonic()-start,flush=True)
(D/f'outputs/sequence-{mode}.json').write_text(json.dumps({'mode':mode,'statistics':stats,'seed':166,'list_universe':[[0,1],[0,2],[1,2]],'counterexamples':[]},indent=2))
