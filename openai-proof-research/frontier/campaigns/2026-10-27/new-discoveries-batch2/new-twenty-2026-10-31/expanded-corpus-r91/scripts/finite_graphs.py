import itertools,json,pathlib,time
D=pathlib.Path(__file__).resolve().parents[1];out=[]
def connected(adj,mask):
 if not mask:return False
 seen=mask&-mask;front=seen
 while front:
  i=(front&-front).bit_length()-1;front &= front-1;new=adj[i]&mask&~seen;seen|=new;front|=new
 return seen==mask
def degenerate(adj):
 mask=(1<<len(adj))-1;d=0
 while mask:
  i=min((i for i in range(len(adj)) if mask>>i&1),key=lambda i:(adj[i]&mask).bit_count());d=max(d,(adj[i]&mask).bit_count());mask^=1<<i
 return max(1,d)
def pcf(adj,lists):
 n=len(adj);col=[-1]*n;order=sorted(range(n),key=lambda i:(len(lists[i]),-adj[i].bit_count()))
 def go(k):
  if k==n:
   for v in range(n):
    ns=[col[i] for i in range(n) if adj[v]>>i&1]
    if ns and not any(ns.count(a)==1 for a in ns):return False
   return True
  v=order[k]
  for c in lists[v]:
   if any(col[u]==c and adj[v]>>u&1 for u in range(n)):continue
   col[v]=c
   # fully colored neighborhoods can be checked early
   ok=True
   for u in range(n):
    ns=[col[i] for i in range(n) if adj[u]>>i&1]
    if ns and -1 not in ns and not any(ns.count(a)==1 for a in ns):ok=False;break
   if ok and go(k+1):return True
  col[v]=-1;return False
 return go(0)
def treecode(adj,v,p):return '('+''.join(sorted(treecode(adj,w,v) for w in range(len(adj)) if adj[v]>>w&1 and w!=p))+')'
for n in range(2,6):
 pairs=list(itertools.combinations(range(n),2));pc=0;fails=[];reg=[];flows=0;flowfail=[]
 for mask in range(1<<len(pairs)):
  edges=[e for k,e in enumerate(pairs) if mask>>k&1];adj=[0]*n
  for a,b in edges:adj[a]|=1<<b;adj[b]|=1<<a
  if not connected(adj,(1<<n)-1):continue
  d=degenerate(adj)
  if not (n==5 and all(a.bit_count()==2 for a in adj)):
   pc+=1
   if not pcf(adj,[list(range(a.bit_count()+d)) for a in adj]):fails.append(mask)
  if len({a.bit_count() for a in adj})==1 and adj[0].bit_count()>=3:
   codes=set();nt=0
   for es in itertools.combinations(edges,n-1):
    ta=[0]*n
    for a,b in es:ta[a]|=1<<b;ta[b]|=1<<a
    if connected(ta,(1<<n)-1):nt+=1;codes.add(min(treecode(ta,v,-1) for v in range(n)))
   reg.append(dict(mask=mask,degree=adj[0].bit_count(),spanning_trees=nt,unlabelled=len(codes)))
  if any(not connected([a&~(1<<v) if u==w else a for u,a in enumerate(adj)],(1<<n)-1) for w,v in []):pass
  # Direct test for bridges; then enumerate cycle-space Z2^2 flows by edge assignments with vertex propagation.
  bridge=False
  for a,b in edges:
   aa=adj[:];aa[a]^=1<<b;aa[b]^=1<<a
   if not connected(aa,(1<<n)-1):bridge=True;break
  if not bridge:
   flows+=1;bal=[0]*n
   def go(k):
    if k==len(edges):return not any(bal)
    a,b=edges[k]
    for c in [1,2,3]:
     bal[a]^=c;bal[b]^=c
     ok=all(bal[v]==0 for v in range(n) if not any(v in e for e in edges[k+1:]))
     ans=ok and go(k+1);bal[a]^=c;bal[b]^=c
     if ans:return True
    return False
   if not go(0):flowfail.append(mask)
 r=dict(n=n,connected_nonC5_prefix_list_tests=pc,pcf_failures=fails,bridgeless_graphs=flows,z2sq_flow_failures=flowfail,regular_spanning_tree_tests=reg)
 out.append(r);print(json.dumps(r),flush=True)
(D/'outputs/finite-graphs.json').write_text(json.dumps(out,indent=2)+'\n')
