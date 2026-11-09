import itertools as it,json,pathlib,math,networkx as nx
import itertools as it,json,pathlib,math,sys
def reach(adj,mask,start):
 seen=1<<start
 while True:
  nxt=seen
  for v in range(len(adj)):
   if seen>>v&1:nxt|=adj[v]&mask
  if nxt==seen:return seen==mask
  seen=nxt
def strong(adj,deleted=0):
 mask=((1<<len(adj))-1)^deleted
 if mask==0:return False
 return all(reach(adj,mask,v) for v in range(len(adj)) if mask>>v&1)
def kstrong(adj,k):return len(adj)>k and all(strong(adj,sum(1<<v for v in s)) for j in range(k) for s in it.combinations(range(len(adj)),j))
def acyclic(adj,mask):
 while mask:
  sources=[v for v in range(len(adj)) if mask>>v&1 and not any(adj[u]>>v&1 for u in range(len(adj)) if mask>>u&1)]
  if not sources:return False
  for v in sources:mask^=1<<v
 return True
def dichi(adj):
 n=len(adj)
 for k in range(1,n+1):
  for c in it.product(range(k),repeat=n):
   if c[0]!=0:continue
   if all(acyclic(adj,sum(1<<v for v in range(n) if c[v]==j)) for j in range(k)):return k

D=pathlib.Path(__file__).resolve().parents[1];O={}
def save(i,x):
 O[str(i)]=x;(D/'outputs/finite-more.json').write_text(json.dumps(O,indent=2)+'\n');print(i,x,flush=True)
# Uniform hypergraphs on at most five vertices, all edge subsets.
count=0;bad=[];critical={}
for n in range(2,6):
 for r in range(2,n+1):
  edges=[sum(1<<x for x in e) for e in it.combinations(range(n),r)]
  for mask in range(1<<len(edges)):
   fam=[e for j,e in enumerate(edges) if mask>>j&1];nu=0
   for j in range(1,len(fam)+1):
    if j*r>n:break
    if any(sum(e.bit_count() for e in ss)==(sum(0 for _ in []) if False else __import__('functools').reduce(int.__or__,ss,0)).bit_count() for ss in it.combinations(fam,j)):nu=j
   for st in range(2,n//r+2):
    if n<st*r-1 or nu>=st:continue
    bound=max(math.comb(st*r-1,r),math.comb(n,r)-(math.comb(n-st+1,r) if n-st+1>=r else 0))
    if len(fam)>bound:bad.append([n,r,mask,st])
    count+=1
   for t in range(1,r):
    if not fam or any((a&b).bit_count()<t for a,b in it.combinations(fam,2)):continue
    tau=next(k for k in range(n+1) if any(all((s&e).bit_count()>=t for e in fam) for s in range(1<<n) if s.bit_count()==k))
    if tau==r:critical[str((n,r,t))]=max(len(fam),critical.get(str((n,r,t)),0))
save(375879,dict(domain='All r-uniform hypergraphs on labelled n=2..5, r=2..n; all nonvacuous s with n>=sr-1',tested=count,violations=bad))
save(376392,dict(domain='All uniform hypergraphs on n<=5; exact t-intersection and tau_t=r computed; not a test of existential c threshold',critical_maxima=critical,violations_not_meaningful_for_asymptotic=True))
# All maximum even-intersection path families, n<=4, maximal clique enumeration.
rows=[]
for n in range(1,5):
 paths=[]
 for east in it.combinations(range(2*n),n):
  east=set(east);x=y=0;edges=set()
  for j in range(2*n):
   edges.add((x,y,j in east))
   if j in east:x+=1
   else:y+=1
  paths.append(edges)
 H=nx.Graph();H.add_nodes_from(range(len(paths)));H.add_edges_from((a,b) for a,b in it.combinations(H,2) if len(paths[a]&paths[b])%2==0)
 counts=0;maximum=0
 for c in nx.find_cliques(H):
  maximum=max(maximum,len(c));counts+=len(c)==2**n
 rows.append(dict(n=n,paths=len(paths),maximum=maximum,extremal_families=counts,catalan=math.comb(2*n,n)//(n+1)))
save(376236,dict(domain='All paths and all maximal even-intersection cliques for n=1..4',rows=rows))
# Primitive k=2 out-multigraphs n<=3; each row unordered pair with repetition; enumerate all 2-colorings.
counts=[]
for n in range(1,4):
 graphs=primitive=totalcolor=nonsync=0
 for rows in it.product(list(it.combinations_with_replacement(range(n),2)),repeat=n):
  graphs+=1;adj=[sum(1<<x for x in set(row)) for row in rows]
  if not strong(adj):continue
  G=nx.DiGraph();G.add_nodes_from(range(n));G.add_edges_from((v,w) for v,row in enumerate(rows) for w in row)
  if not nx.is_aperiodic(G):continue
  primitive+=1
  for cs in it.product(range(2),repeat=n):
   maps=[[rows[v][cs[v]^letter] for v in range(n)] for letter in range(2)];seen={tuple(range(n))};stack=list(seen);sync=False
   while stack:
    state=stack.pop()
    if len(state)==1:sync=True;break
    for f in maps:
     nxt=tuple(sorted({f[v] for v in state}))
     if nxt not in seen:seen.add(nxt);stack.append(nxt)
   totalcolor+=1;nonsync+=not sync
 counts.append(dict(n=n,graphs=graphs,primitive=primitive,colors_with_parallel_arcs_distinguished=totalcolor,nonsynchronizing=nonsync))
save(376125,dict(domain='All k=2 out-multigraphs on n=1..3; all locally distinguished colorings; finite diagnostic cannot decide #P completeness',rows=counts))
# All labelled circulants of order 10..14; actual degree >=9 instances.
rows=[]
for n in range(10,15):
 for mask in range(1<<(n//2)):
  G=nx.Graph();G.add_nodes_from(range(n));G.add_edges_from((v,(v+d)%n) for v in range(n) for d in range(1,n//2+1) if mask>>(d-1)&1)
  de=max(dict(G.degree()).values());om=max(map(len,nx.find_cliques(G)))
  if de<9 or om>de-1:continue
  # complement coloring is a clique cover; exact search via independent sets.
  sets=[sum(1<<v for v in s) for s in nx.find_cliques(nx.complement(G))]
  def color(left,k):
   if not left:return True
   if not k:return False
   v=(left&-left)
   return any(color(left&~s,k-1) for s in sets if s&v)
  ok=color((1<<n)-1,de-1);rows.append(dict(n=n,mask=mask,Delta=de,omega=om,bound_satisfied=ok))
save(376009,dict(domain='All undirected circulants n=10..14 (all subsets of step lengths 1..floor(n/2)); nonvacuous Delta>=9 and omega<=Delta-1',eligible=len(rows),rows=rows))
