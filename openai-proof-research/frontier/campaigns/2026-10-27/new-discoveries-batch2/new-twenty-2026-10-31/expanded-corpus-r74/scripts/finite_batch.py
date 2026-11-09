import pathlib,json,itertools,resource,os,sys,time,math
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));D=pathlib.Path(__file__).resolve().parents[1];mode=sys.argv[1];out=[]
def save(r):out.append(r);print(json.dumps(r),flush=True);(D/'outputs'/f'finite-{mode}.json').write_text(json.dumps(out,indent=2))
if mode=='kakeya':
 for q in [3,5,7]:
  # Translate selected horizontal and vertical lines to y=0,x=0, losing no configuration up to translation.
  lines=[[sum(1<<(x*q+(m*x+b)%q) for x in range(q)) for b in range(q)] for m in range(1,q)]
  fixed=sum(1<<y for y in range(q))|sum(1<<(x*q) for x in range(q));best=q*q;count=0;witness=None
  for bs in itertools.product(range(q),repeat=q-1):
   union=fixed
   for m,b in enumerate(bs):union|=lines[m][b]
   sz=union.bit_count();count+=1
   if sz<best:best=sz;witness=bs
  save({'id':379908,'q':q,'configurations':count,'normalization':'horizontal y=0 and vertical x=0; all q intercepts for each other direction','minimum_union':best,'predicted':(q*(q+1)+q-1)//2,'intercepts':witness})
elif mode=='partitions':
 import networkx as nx
 def parts(n):
  def rec(a):
   if len(a)==n:
    yield [sum(1<<i for i,x in enumerate(a) if x==j) for j in range(max(a)+1)];return
   for v in range(max(a)+2):yield from rec(a+[v])
  yield from rec([0])
 for n in range(3,8):
  ps=list(parts(n))
  for k in range(2,n):
   pp=[a for a in ps if len(a)==k];G=nx.Graph();G.add_nodes_from(range(len(pp)))
   for i in range(len(pp)):
    for j in range(i):
     if all((a&b)!=a and (a&b)!=b for a in pp[i] for b in pp[j]):G.add_edge(i,j)
   au=[i for i,p in enumerate(pp) if max(a.bit_count() for a in p)-min(a.bit_count() for a in p)<=1]
   best=max(map(len,nx.find_cliques(G)),default=0);ba=max(map(len,nx.find_cliques(G.subgraph(au))),default=0)
   save({'id':380350,'n':n,'k':k,'all_partitions':len(pp),'almost_uniform':len(au),'largest_system':best,'largest_almost_uniform_system':ba})
elif mode=='trees':
 import networkx as nx
 def moments(G):
  n=len(G);A=[[int(G.has_edge(i,j)) for j in range(n)] for i in range(n)];B=[[int(i==j) for j in range(n)] for i in range(n)];res=[]
  for k in range(1,9):
   B=[[sum(B[i][v] for v in G.neighbors(j)) for j in range(n)] for i in range(n)]
   if k in [4,6,8]:res.append(sum(B[i][i] for i in range(n)))
  return res
 for n in range(2,14):
  trees=[nx.convert_node_labels_to_integers(T) for T in nx.nonisomorphic_trees(n)];bad=[]
  for delta in range(2,n):
   G=nx.Graph();G.add_node(0);nxt=1
   for i in range(n):
    for j in range(delta if i==0 else delta-1):
     if nxt<n:G.add_edge(i,nxt);nxt+=1
   bound=moments(G)
   for T in trees:
    if max(dict(T.degree()).values())==delta:
     mm=moments(T)
     if any(a>b for a,b in zip(mm,bound)):bad.append({'delta':delta,'edges':list(T.edges()),'moments':mm,'bound':bound})
  save({'id':381160,'n':n,'unlabeled_trees':len(trees),'even_moments':[4,6,8],'bad':bad})
elif mode=='parity':
 for n in [1,2,3]:
  es=[(i,n+j) for i in range(n) for j in range(n)];summary=[]
  for colors in range(n,2**((n-1).bit_length())+1):
   used=[set() for _ in range(2*n)];assign=[];counts=[0,0];solutions=[]
   def check():
    adj=[[] for _ in range(2*n)]
    for (u,v),c in zip(es,assign):adj[u].append((v,c));adj[v].append((u,c))
    def dfs(u,vis,parity):
     for v,c in adj[u]:
      if not vis>>v&1:
       p=parity^(1<<c)
       if p==0 or not dfs(v,vis|(1<<v),p):return False
     return True
    return all(dfs(u,1<<u,0) for u in range(2*n))
   def rec(t,maxc):
    if t==len(es):
     counts[0]+=1
     if check():counts[1]+=1;solutions.append(assign.copy())
     return
    u,v=es[t]
    for c in range(min(colors,maxc+2)):
     if c in used[u] or c in used[v]:continue
     used[u].add(c);used[v].add(c);assign.append(c);rec(t+1,max(maxc,c));assign.pop();used[u].remove(c);used[v].remove(c)
   rec(0,-1);summary.append({'colors':colors,'proper_colorings_mod_color_permutation':counts[0],'parity_colorings':counts[1],'first_witness':solutions[:1]})
  save({'id':379584,'n':n,'source_corrected_ceiling':True,'space':'all proper edge colorings up to color relabeling; all simple paths checked; not strong parity walks','results':summary})
