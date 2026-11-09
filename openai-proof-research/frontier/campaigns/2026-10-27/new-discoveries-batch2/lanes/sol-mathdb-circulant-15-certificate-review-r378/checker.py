"""Independent mask enumeration / Kosaraju certificate. No author code imported.
Replay: checker.py verify. Produce certificate: checker.py build.
Binary records: 15 label bytes, little-endian uint32 monotone rank, 1 parity byte.
"""
from pathlib import Path
import sys,json,struct,collections,itertools,math
P=Path(__file__).parent
# Enumerate ALL signed walks of length <=3, rather than author's BFS.
D={}
for k in range(1,4):
 for steps in itertools.product((-5,-1,1,5),repeat=k):
  x=abs(sum(steps))
  if x:D[x]=max(D.get(x,0),4-k)
assert D=={1:3,2:2,3:1,4:2,5:3,6:2,7:1,9:1,10:2,11:1,15:1}
D=sorted(D.items()); full=(1<<14)-1
allowed=[[sum(1<<y for y in range(14) if abs(x-y)>=r) for x in range(14)] for r in range(4)]
counts=[0]*16; states=[]
def mask(w):
 m=full
 for d,r in D:
  if d>len(w):break
  m &= allowed[r][w[-d]]
 return m
def visit(w):
 counts[len(w)]+=1
 if len(w)==15:states.append(w);return
 m=mask(w)
 while m:
  b=m&-m;m-=b;visit(w+bytes([b.bit_length()-1]))
visit(b'')
index={w:i for i,w in enumerate(states)}; N=len(states)
# Edges independently derived by suffix membership, then check distance-15 constraint.
# Every suffix target is a valid state; distance 15 is the sole missing pair.
prefix=collections.defaultdict(list)
for i,w in enumerate(states):prefix[w[:14]].append(i)
adj=[[] for _ in states]; rev=[[] for _ in states]
for i,w in enumerate(states):
 for j in prefix.get(w[1:],[]):
  if w[0]!=states[j][-1]:adj[i].append(j);rev[j].append(i)
E=sum(map(len,adj))
if sys.argv[1]=='build':
 # Kosaraju: finish-order DFS then reverse graph flood, different from author's Tarjan.
 seen=bytearray(N);order=[]
 for root in range(N):
  if seen[root]:continue
  seen[root]=1; stack=[(root,0)]
  while stack:
   u,k=stack[-1]
   if k==len(adj[u]):order.append(u);stack.pop();continue
   v=adj[u][k];stack[-1]=(u,k+1)
   if not seen[v]:seen[v]=1;stack.append((v,0))
 rank=[-1]*N; color=bytearray(N); members=[]
 for root in reversed(order):
  if rank[root]>=0:continue
  c=len(members);mem=[];stack=[root];rank[root]=c
  while stack:
   u=stack.pop();mem.append(u)
   for v in rev[u]:
    if rank[v]<0:rank[v]=c;stack.append(v)
  members.append(mem)
 hist=collections.Counter();periods=collections.Counter()
 for c,mem in enumerate(members):
  assigned={mem[0]};queue=collections.deque([mem[0]])
  while queue:
   u=queue.popleft()
   for v in adj[u]:
    if rank[v]!=c:continue
    if v not in assigned:assigned.add(v);color[v]=1-color[u];queue.append(v)
    assert color[v]!=color[u]
  assert len(assigned)==len(mem)
  if len(mem)>1:
   hist[len(mem)]+=1
   level={mem[0]:0}; queue=collections.deque([mem[0]])
   while queue:
    u=queue.popleft()
    for v in adj[u]:
     if rank[v]==c and v not in level:level[v]=level[u]+1;queue.append(v)
   period=0
   for u in mem:
    for v in adj[u]:
     if rank[v]==c:period=math.gcd(period,level[u]+1-level[v])
   periods[str((len(mem),period))]+=1
 with (P/'lower.bin').open('wb') as f:
  for i,w in enumerate(states):f.write(w+struct.pack('<IB',rank[i],color[i]))
 (P/'lower-generation.json').write_text(json.dumps(dict(states=N,edges=E,prefix_counts=counts,nontrivial_scc_size_histogram=dict(hist),size_period_histogram=dict(periods)),indent=2)+'\n')
else:
 data=(P/'lower.bin').read_bytes();assert len(data)==20*N
 rank=[];color=[]
 for i,w in enumerate(states):
  row=data[20*i:20*i+20];assert row[:15]==w
  a,b=struct.unpack('<IB',row[15:]);assert b in (0,1);rank.append(a);color.append(b)
# This check does not rely on SCC correctness: ranks never decrease; equal-rank
# edges flip parity. A closed walk has constant rank and hence even length.
if sys.argv[1]=='negative':
 u,v=next((u,v) for u in range(N) for v in adj[u] if rank[u]==rank[v]);color[u]^=1
for u in range(N):
 for v in adj[u]:assert rank[v]>rank[u] or (rank[v]==rank[u] and color[u]!=color[v])
assert (N,E)==(110672,111010)
print(json.dumps(dict(mode=sys.argv[1],states=N,edges=E,prefix_counts=counts,all_edges_rank_parity_checked=True)))
