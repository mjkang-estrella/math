import itertools,random,json
from pathlib import Path
random.seed(156);out={}
# literal graph coloring and induced K4 subdivisions on every labelled graph <=6 vertices.
def color(n,E,k):
 adj=[set() for _ in range(n)]
 for a,b in E:adj[a].add(b);adj[b].add(a)
 order=sorted(range(n),key=lambda a:-len(adj[a]));c=[-1]*n
 def dfs(j):
  if j==n:return True
  v=order[j]
  for x in range(k):
   if all(c[w]!=x for w in adj[v]):
    c[v]=x
    if dfs(j+1):return True
  c[v]=-1;return False
 return dfs(0)
def isk4(n,E):
 for m in range(4,n+1):
  for S in itertools.combinations(range(n),m):
   A={v:set() for v in S}
   for a,b in E:
    if a in A and b in A:A[a].add(b);A[b].add(a)
   if sorted(map(len,A.values()))!=[2]*(m-4)+[3]*4:continue
   while any(len(N)==2 for N in A.values()):
    v=next(v for v in A if len(A[v])==2);a,b=A[v];del A[v];A[a].remove(v);A[b].remove(v);A[a].add(b);A[b].add(a)
   if len(A)==4 and all(len(N)==3 for N in A.values()):return True
 return False
rows=[]
for n in range(4,7):
 edges=list(itertools.combinations(range(n),2));badcolor=0;candidate=0
 for mask in range(1<<len(edges)):
  E={edges[i] for i in range(len(edges)) if mask>>i&1}
  if color(n,E,4):continue
  badcolor+=1
  if not isk4(n,E):candidate+=1
 assert candidate==0;rows.append({'n':n,'all_labelled_graphs':1<<len(edges),'not_4colorable':badcolor,'isk4free_not4colorable':candidate})
out['326282']=rows
# Standard (2,2) decomposition: edge label red1,red2,blue1,blue2; only same-color edges checked.
rows=[]
for n in range(4,6):
 edges=list(itertools.combinations(range(n),2));count=0;labellings=0
 for mask in range(1<<len(edges)):
  E=[edges[i] for i in range(len(edges)) if mask>>i&1]
  adj=[set() for _ in range(n)]
  for a,b in E:adj[a].add(b);adj[b].add(a)
  seen={0}
  while True:
   new=seen|set().union(*(adj[v] for v in seen))
   if new==seen:break
   seen=new
  if len(seen)!=n:continue
  count+=1;found=False
  for L in itertools.product(range(4),repeat=len(E)):
   labellings+=1;sums=[[0]*n for _ in range(2)]
   for (a,b),l in zip(E,L):sums[l//2][a]+=l%2+1;sums[l//2][b]+=l%2+1
   if all(sums[l//2][a]!=sums[l//2][b] for (a,b),l in zip(E,L)):found=True;break
  assert found
 rows.append({'n':n,'connected_labelled_graphs_exhausted':count,'edge_labellings_checked_until_witness':labellings})
out['355759']=rows
# 4-regular bipartite: samples and explicit disconnected spanning 2-factor search.
rows=[]
for n in range(4,11):
 tested=0;attempts=0
 while tested<50 and attempts<5000:
  attempts+=1;Ps=[random.sample(range(n),n) for _ in range(4)]
  if any(len({P[i] for P in Ps})<4 for i in range(n)):continue
  A=[{P[i] for P in Ps} for i in range(n)];choice=[];deg=[0]*n;found=[False]
  def dfs(i):
   if found[0]:return
   if i==n:
    if any(d!=2 for d in deg):return
    adj=[set() for _ in range(2*n)]
    for a,C in enumerate(choice):
     for b in C:adj[a].add(b+n);adj[b+n].add(a)
    seen={0};stack=[0]
    while stack:
     for w in adj[stack.pop()]-seen:seen.add(w);stack.append(w)
    if len(seen)<2*n:found[0]=True
    return
   for C in itertools.combinations(A[i],2):
    if any(deg[b]>=2 for b in C):continue
    for b in C:deg[b]+=1
    choice.append(C);dfs(i+1);choice.pop()
    for b in C:deg[b]-=1
  dfs(0);assert found[0];tested+=1
 rows.append({'side_size':n,'4regular_bipartite_graphs_tested':tested,'permutation_tuples_sampled':attempts})
out['364299']=rows
Path('outputs/graph-small-search.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
