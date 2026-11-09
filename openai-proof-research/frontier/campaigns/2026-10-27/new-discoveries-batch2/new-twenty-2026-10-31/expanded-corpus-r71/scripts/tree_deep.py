import networkx as nx,itertools as it,json,pathlib,time,math
D=pathlib.Path(__file__).resolve().parents[1];trees={}
for k in [6,7,8]:
 trees[k]=[]
 for T in nx.nonisomorphic_trees(k):
  root=max(T,key=T.degree);parent={root:-1};order=[root]
  for v in order:
   for w in sorted(T[v],key=T.degree,reverse=True):
    if w not in parent:parent[w]=v;order.append(w)
  trees[k].append((order,parent,dict(T.degree())))
def embeds(adj,T):
 order,par,deg=T;maps={}
 def go(i,used):
  if i==len(order):return True
  v=order[i];pool=((1<<8)-1) if i==0 else adj[maps[par[v]]]
  pool&=~used
  for w in range(8):
   if pool>>w&1 and adj[w].bit_count()>=deg[v]:
    maps[v]=w
    if go(i+1,used|1<<w):return True
  return False
 return go(0,0)
count=tests=0;bad=[];start=time.monotonic();atlas=[G for G in nx.graph_atlas_g() if len(G)==7]
for ix,G in enumerate(atlas):
 base=[sum(1<<w for w in G[v]) for v in G]
 for mask in range(128):
  adj=[base[v]|((1<<7) if mask>>v&1 else 0) for v in range(7)]+[mask];counts={r:0 for r in range(3,9)}
  # enumerate cliques through ascending extension
  def cliques(pool,size):
   while pool:
    b=pool&-pool;pool-=b;v=b.bit_length()-1;s=size+1
    if s>=3:counts[s]+=1
    cliques(pool&adj[v],s)
  cliques(255,0)
  for k in trees:
   a,b=divmod(8,k-1)
   rs=[r for r in range(3,k) if counts[r]>a*math.comb(k-1,r)+math.comb(b,r)]
   if not rs:continue
   for T in trees[k]:
    tests+=1
    if not embeds(adj,T):bad.append({'base_atlas_index':ix,'neighbor_mask':mask,'k':k,'r':rs,'tree':T})
  count+=1
 if ix%20==0:print(json.dumps({'completed_bases':ix+1,'total_bases':len(atlas),'hosts':count,'embedding_tests':tests,'counterexamples':len(bad),'seconds':time.monotonic()-start}),flush=True)
(D/'outputs/tree-deep.json').write_text(json.dumps({'domain':'Every unlabelled 8-vertex graph is represented: add one vertex with each of 128 neighborhoods to each of 1044 unlabelled seven-vertex graphs; duplicates retained. All tree shapes k=6,7,8; all r=3..k-1. Exact non-induced injective embedding search on hosts exceeding formula only.','hosts':count,'tree_counts':{k:len(v) for k,v in trees.items()},'embedding_tests':tests,'violations':bad,'seconds':time.monotonic()-start},indent=2)+'\n')
