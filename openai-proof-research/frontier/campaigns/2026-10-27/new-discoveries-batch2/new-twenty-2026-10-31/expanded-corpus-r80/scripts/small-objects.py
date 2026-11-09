import json,pathlib,sys,itertools,functools,collections,math
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'outputs/python-packages'));import networkx as nx
mode=sys.argv[1]
def save(o):
 (D/f'outputs/{mode}.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o)[-3000:],flush=True)
if mode=='cordial':
 rows=[]
 for n in range(2,9):
  for gi,g in enumerate(nx.nonisomorphic_trees(n)):
   for k in [2,3,4]:
    found=None;tested=0
    for c in itertools.product(range(k),repeat=n):
     counts=[c.count(i) for i in range(k)]
     if max(counts)-min(counts)>1:continue
     tested+=1;edges=[0]*k
     for a,b in g.edges():edges[(c[a]+c[b])%k]+=1
     if max(edges)-min(edges)<=1:found=c;break
    rows.append(dict(n=n,tree_index=gi,k=k,tested_balanced_assignments=tested,edges=list(g.edges()),labeling=found))
 save({'interpretation':'cyclic groups only; witness search stops when found; failure exhausts every balanced assignment; finite failures cannot refute weak cordiality','rows':rows})
if mode=='pqs':
 def sortable(p):
  for cut in range(1<<(len(p)-1)):
   out=[];start=0
   for j in range(len(p)-1):
    if cut>>j&1:out+=p[start:j+1][::-1];start=j+1
   out+=p[start:][::-1]
   if not any(out[i]>out[k]>out[j] for i in range(len(p)) for j in range(i+1,len(p)) for k in range(j+1,len(p))):
    # 231 is out[j] > out[i] > out[k], fix explicitly below.
    pass
   if not any(out[j]>out[i]>out[k] for i in range(len(p)) for j in range(i+1,len(p)) for k in range(j+1,len(p))):return True
  return False
 rows=[]
 for n in range(1,8):
  count=sum(sortable(list(p)) for p in itertools.permutations(range(n)))
  rows.append({'n':n,'permutations':math.factorial(n),'sortable':count});save(rows)
if mode=='prime-squares':
 import sympy as s
 pairs=[(x,y) for x in range(2,301) for y in range(1,x) if s.isprime(x+y+1) and s.isprime(x*y+1)]
 sums=[]
 for mask in range(1,1<<12):
  e=[(i+1)**2 for i in range(12) if mask>>i&1];c=collections.Counter(a+b for a in e for b in e)
  sums.append((mask,len(e),len(c),sum(v*v for v in c.values())))
 save({'prime_pair_box':'1<=y<x<=300','prime_witnesses':pairs,'squares_universe':'1^2..12^2','all_nonempty_subsets':sums,'limitation':'asymptotic existential constants are not tested by finitely many ratios'})
if mode=='core':
 from sympy.utilities.iterables import partitions
 rows=[];sc6={}
 for n in range(1,31):
  counts=collections.Counter();sc=0
  for p in partitions(n):
   lam=sorted([i for i,m in p.items() for _ in range(m)],reverse=True);col=[sum(v>j for v in lam) for j in range(lam[0])]
   hooks={lam[i]-j+col[j]-i-1 for i in range(len(lam)) for j in range(lam[i])}
   for t in range(4,n+1):
    if all(h%t for h in hooks):counts[t]+=1
   if lam==col and all(h%6 for h in hooks):sc+=1
  rows.append({'n':n,'core_counts':dict(counts),'sc6':sc});save(rows)
if mode=='list-coloring':
 rows=[]
 def colorable(G,lists):
  order=sorted(G,key=lambda v:-G.degree[v]);c={}
  def go(j):
   if j==len(order):return True
   u=order[j]
   for v in lists[u]:
    if all(c.get(w)!=v for w in G[u]):
     c[u]=v
     if go(j+1):return True
     del c[u]
   return False
  return go(0)
 for gi,G in enumerate(nx.graph_atlas_g()):
  n=len(G)
  if not 1<=n<=4:continue
  if any(G.degree(v)>=3 and any(not any(G.has_edge(a,b) for a,b in itertools.combinations(S,2)) for S in itertools.combinations(G[v],3)) for v in G):continue
  chi=next(k for k in range(1,n+1) if colorable(G,[tuple(range(k))]*n))
  lists=list(itertools.combinations(range(4),chi));tested=0;witness=None
  for L in itertools.product(lists,repeat=n):
   tested+=1
   if not colorable(G,L):witness=L;break
  rows.append(dict(graph_atlas=gi,n=n,chi=chi,palette=4,list_assignments_tested=tested,witness=witness))
 save(rows)
