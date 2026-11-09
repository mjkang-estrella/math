import sys,pathlib,itertools,json,time,random,collections
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'fresh-corpus-r10/pydeps'))
import networkx as nx
rng=random.Random(215);start=time.monotonic();counts=collections.Counter();bad=[]
def check(G,label):
 G=nx.convert_node_labels_to_integers(G);n=len(G);adj=[set(G[v]) for v in range(n)]
 deg=list(map(len,adj));three=[v for v in range(n) if deg[v]==3]
 if max(deg,default=0)>3 or any(deg[u]==3 for v in three for u in adj[v]):return
 if any(not any(w in adj[z] for u in adj[v] for z in adj[u]-{v} for w in adj[v]-{u}) for v in three):
  # The above tests 4-cycles; separately allow triangles.
  if any(not(any(z in adj[v] for u in adj[v] for z in adj[u]-{v}) or any(w in adj[z] for u in adj[v] for z in adj[u]-{v} for w in adj[v]-{u})) for v in three):return
 near=[[set() for _ in range(5)] for _ in range(n)]
 for v in range(n):
  seen={v};front={v}
  for c in range(1,5):front=set().union(*(adj[u] for u in front))-seen if front else set();seen|=front;near[v][c]=seen-{v}
 dom=[15]*n
 def rec(left):
  if not left:return True
  v=min(left,key=lambda u:dom[u].bit_count());opts=dom[v]
  for c in range(4):
   if not opts>>c&1:continue
   changes=[];ok=True
   for u in near[v][c+1]&left:
    old=dom[u];new=old&~(1<<c)
    if old!=new:changes.append((u,old));dom[u]=new
    if not new:ok=False;break
   if ok and rec(left-{v}):return True
   for u,x in changes:dom[u]=x
  return False
 ans=rec(set(range(n)));counts[label]+=1
 if not ans:bad.append({'label':label,'n':n,'edges':sorted(G.edges())});print('BAD',bad[-1],flush=True)
def bead(lengths,end=0):
 G=nx.Graph();ports=[]
 def path(u,v,l):
  prev=u
  for _ in range(l-1):w=len(G);G.add_node(w);G.add_edge(prev,w);prev=w
  G.add_edge(prev,v)
 for _ in lengths:
  a=len(G);b=a+1;G.add_nodes_from([a,b]);path(a,b,2);path(a,b,2);ports.append((a,b))
 for i,l in enumerate(lengths[:-1]):path(ports[i][1],ports[i+1][0],l)
 if end==0:path(ports[-1][1],ports[0][0],lengths[-1])
 else:
  for u in [ports[0][0],ports[-1][1]]:
   w=len(G);G.add_node(w);path(u,w,lengths[-1]);path(w,w,end)
 return G
for G in nx.graph_atlas_g():
 if len(G) and nx.is_connected(G):check(G,'atlas-'+str(len(G)))
for k in range(1,8):
 seqs=list(itertools.product(range(2,6),repeat=k)) if k<=4 else [tuple(rng.randint(2,12) for _ in range(k)) for _ in range(500)]
 for ls in seqs:
  for end in [0,3,4]:check(bead(ls,end),'bead-'+str(k)+'-end'+str(end))
  if bad or time.monotonic()-start>100:break
 if bad or time.monotonic()-start>100:break
(D/'outputs/packing-corrected.json').write_text(json.dumps({'counts':counts,'bad':bad,'wall':time.monotonic()-start,'scope':'Connected atlas through order 7 filtered by exact degrees/local-cycle tests; generated necklaces and end-loop chains of K2,2 blocks. No completeness claim for generated family.'},indent=2)+'\n')
print(dict(counts),bad,flush=True)
