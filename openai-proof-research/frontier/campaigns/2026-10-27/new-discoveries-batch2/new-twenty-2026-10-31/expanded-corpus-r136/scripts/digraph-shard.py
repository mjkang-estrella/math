import pathlib,sys,itertools,json,collections,time
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'sources/vendor/networkx-networkx-3.4.2'));import networkx as nx
n=int(sys.argv[1]);full=(1<<n)-1;target=n*n+3*n-4
# For outradius3 and W<=target: max outdegree<=n-3 and m>n*(n-4).
# Relabel a degree(n-3) vertex0; fix its neighbors1..n-3.
# Total degree deficit from n-3 is at most n-4.
options=[]
for i in range(n):options.append([(sum(1<<j for j in s),n-3-d) for d in range(n-3,0,-1) for s in itertools.combinations([j for j in range(n) if j!=i],d)])
a=[sum(1<<j for j in range(1,n-2))]+[0]*(n-1);nodes=collections.Counter();found=[];sig=collections.Counter();complete=0;checks=0
bases=[]
for s in range(1,(n-4)//2+1):
 types=[0]*s+[1,2]+[3]*(n-4-s)+[4,5];g=nx.DiGraph();g.add_nodes_from(range(n))
 for u,x in enumerate(types):
  for v,y in enumerate(types):
   if u!=v and (x==y or x//3==y//3 and y%3<=x%3+1 or x//3!=y//3 and y%3==0):g.add_edge(u,v)
 bases.append(g)
def check():
 global complete,checks
 complete+=1;W=0;ec=[]
 for u in range(n):
  seen=1<<u;front=seen;w=0;dist=0
  while front:
   seen|=front;w+=dist*front.bit_count();bits=front;nxt=0
   while bits:
    b=bits&-bits;bits-=b;nxt|=a[b.bit_length()-1]
   front=nxt&~seen;dist+=1
  if seen!=full:return
  W+=w;ec.append(dist-1)
  if W>target:return
 if min(ec)!=3:return
 checks+=1;g=nx.DiGraph();g.add_nodes_from(range(n));g.add_edges_from((u,v) for u in range(n) for v in range(n) if a[u]>>v&1)
 iso=any(nx.is_isomorphic(g,b) for b in bases);sig[str((W,iso))]+=1
 if W<target or not iso:found.append({'adj':a[:],'W':W,'ecc':ec,'iso':iso});print('CANDIDATE',found[-1],flush=True)
def rec(i,deficit):
 nodes[i]+=1
 if i==n:check();return
 groups={}
 for v in range(i+1,n):
  key=tuple(bool(a[u]>>v&1) for u in range(i));groups.setdefault(key,[]).append(v)
 groups=list(groups.values())
 for idx,(mask,d) in enumerate(options[i]):
  if i==1 and not (int(sys.argv[2])<=idx<int(sys.argv[3])):continue
  if deficit+d>n-4:continue
  if any(any((mask>>vs[j]&1) < (mask>>vs[j+1]&1) for j in range(len(vs)-1)) for vs in groups):continue
  a[i]=mask;valid=True
  # Any assigned row whose currently known 2-neighborhood is full can be pruned.
  for u in range(i+1):
   seen=(1<<u)|a[u];bits=a[u]&((1<<(i+1))-1)
   while bits:
    b=bits&-bits;bits-=b;seen|=a[b.bit_length()-1]
   if seen==full:valid=False;break
  if valid:rec(i+1,deficit+d)
  if i==1:print("finished row1 option",idx,"nodes",dict(nodes),flush=True)
  a[i]=0
rec(1,0)
out={'n':n,'target':target,'partial_nodes_by_depth':dict(nodes),'completed_matrices':complete,'qualifying':checks,'outcomes':dict(sig),'candidates':found};print(json.dumps(out),flush=True);(D/f'outputs/digraph-shard-{n}-{sys.argv[2]}-{sys.argv[3]}.json').write_text(json.dumps(out,indent=2)+'\n')
