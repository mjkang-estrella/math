import sys;sys.path.insert(0,'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/fresh-corpus-r10/pydeps')
import networkx as nx,random,itertools,pathlib,json
L=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(152);out=[]
for n in range(8,13):
 for sample in range(20):
  G=nx.path_graph(n);pairs=list(nx.non_edges(G));rng.shuffle(pairs)
  for u,v in pairs[:rng.randrange(len(pairs)+1)]:
   G.add_edge(u,v)
   if not nx.check_planarity(G)[0]:G.remove_edge(u,v)
  m=G.number_of_edges();adj=[sum(1<<v for v in G[u]) for u in G];N=1<<n;e=[0]*N;cl=[True]*N;dp=[0]*N;cc=[0]*N
  for S in range(1,N):
   bit=S&-S;i=bit.bit_length()-1;T=S^bit;e[S]=e[T]+(adj[i]&T).bit_count();cl[S]=cl[T] and (adj[i]&T)==T;dp[S]=-10000;cc[S]=n
   U=T
   while True:
    B=U|bit;R=S^B;dp[S]=max(dp[S],2+e[B]+dp[R])
    if cl[B]:cc[S]=min(cc[S],1+cc[R])
    if U==0:break
    U=(U-1)&T
  y=dp[-1]-m-1;lam=1 if list(nx.bridges(G)) else 2;bd=2*cc[-1]-lam+1
  r=dict(n=n,sample=sample,m=m,y=y,complement_chromatic=cc[-1],lambda_lower=lam,bound=bd,violation=y>bd)
  if r['violation']:r['edges']=list(G.edges())
  out.append(r);print(json.dumps(r),flush=True);(L/'outputs/planar.json').write_text(json.dumps(out,indent=2))
