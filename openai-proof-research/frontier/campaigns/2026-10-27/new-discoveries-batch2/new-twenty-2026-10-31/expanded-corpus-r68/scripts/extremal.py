import networkx as nx,random,numpy as np,json,pathlib,itertools,time,sympy as sp
D=pathlib.Path(__file__).resolve().parents[1];random.seed(683230);start=time.monotonic()
def mostar(g):
 ds=dict(nx.all_pairs_shortest_path_length(g));return sum(abs(sum(ds[x][u]<ds[x][v] for x in g)-sum(ds[x][u]>ds[x][v] for x in g)) for u,v in g.edges())
def c4(g):
 return all(len(set(g[u])&set(g[v]))<=1 for u,v in itertools.combinations(g,2))
def tau(g,exact=False):
 a=nx.to_numpy_array(g,dtype=int);l=np.diag(a.sum(axis=1))-a
 return int(sp.det(sp.Matrix(l[:-1,:-1]))) if exact else max(0,round(np.linalg.det(l[:-1,:-1])))
# Structural blow-ups: base distances determine all intercluster distances.
def blow_score(h,w,cl):
 ds=dict(nx.all_pairs_shortest_path_length(h));n=sum(w);deg=[sum(w[j] for j in h[i])+(w[i]-1 if cl[i] else 0) for i in h];s=0
 for i,j in h.edges():
  # endpoints contribute 1 each, other vertices in endpoint cluster use 1 or 2.
  z=0
  for k in h:
   if k==i:z+=(w[i]-1)*(0 if cl[i] else -1)+1
   elif k==j:z-=(w[j]-1)*(0 if cl[j] else -1)+1
   else:z+=w[k]*((ds[k][i]<ds[k][j])-(ds[k][i]>ds[k][j]))
  s+=w[i]*w[j]*abs(z)
 return s
out={'seed':683230,'mostar':[],'spanning_atlas':[],'spanning_random':[]}
bases=[h for h in nx.graph_atlas_g() if 2<=len(h)<=5 and nx.is_connected(h)]
for n in [12,18,24,36]:
 best=(-1,None);count=0
 for h in bases:
  k=len(h)
  for z in range(30):
   cuts=sorted(random.sample(range(1,n),k-1));w=np.diff([0]+cuts+[n]).tolist();cl=[bool(random.getrandbits(1)) for _ in h];v=blow_score(h,w,cl);count+=1
   if v>best[0]:best=(v,{'base_edges':list(h.edges()),'weights':w,'cliques':cl})
 ref=(n//3)*(n-n//3)*(n-n//3-1)
 out['mostar'].append({'n':n,'evaluations':count,'best':best,'conjectured':ref})
for n in [4,5,6,7]:
 gs=[g for g in nx.graph_atlas_g() if len(g)==n and nx.is_connected(g) and c4(g)];best=max(gs,key=lambda g:tau(g));out['spanning_atlas'].append({'n':n,'graphs':len(gs),'best_tau_exact':tau(best,True),'edges':list(best.edges())})
for n in [13,21]:
 best=(0,None);count=0
 for r in range(350):
  g=nx.empty_graph(n);pairs=list(itertools.combinations(range(n),2));random.shuffle(pairs)
  for u,v in pairs:
   g.add_edge(u,v)
   if not c4(g):g.remove_edge(u,v)
  val=tau(g);count+=1
  if val>best[0]:best=(val,g.copy())
 out['spanning_random'].append({'n':n,'evaluations':count,'best_tau_exact':tau(best[1],True),'edges':list(best[1].edges()),'target':n**((n-3)//2)})
out['seconds']=time.monotonic()-start;(D/'outputs/extremal.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
