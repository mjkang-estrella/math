import networkx as nx,random,math,json,itertools
random.seed(129)
def gamma(G,k):
 n=len(G);w=[7**i for i in range(n-1)]+[0];steps=[w[a]-w[b] for a,b in G.edges()];steps+= [-s for s in steps];S={0};L=[1]
 for t in range(1,k+1):S.update({a+b for a in S for b in steps});L.append(len(S))
 h=[sum((-1)**j*math.comb(n,j)*L[i-j] for j in range(i+1)) for i in range(k+1)];ga=[]
 for i in range(k+1):ga.append(h[i]-sum(ga[j]*math.comb(n-1-2*j,i-j) for j in range(i)))
 return ga,L
cases=[]
for G in nx.graph_atlas_g():
 if len(G)==7 and min(dict(G.degree()).values())>=3 and nx.node_connectivity(G)>=3:cases.append(('atlas',G))
for n in [8,9,10,11]:
 for trial in range(40):
  G=nx.gnp_random_graph(n,random.choice([.4,.5,.6,.7]),seed=random.randint(0,2**30))
  if min(dict(G.degree()).values())>=3 and nx.node_connectivity(G)>=3:cases.append(('random',G))
 for extra in range(5):
  G=nx.complete_bipartite_graph(3,n-3)
  for a,b in itertools.combinations(range(3),2):
   if extra&1:G.add_edge(a,b)
  if extra>=2:G.add_edge(3,4)
  if extra>=3:G.remove_edge(0,3)
  if nx.node_connectivity(G)>=3:cases.append(('structured',G))
for typ,G in cases:
 ga,L=gamma(G,3);n=len(G)
 expected=False
 for A in itertools.combinations(range(n),3):
  B=set(G)-set(A)
  if all(G.has_edge(a,b) for a in A for b in B) and not any(G.has_edge(a,b) for a,b in itertools.combinations(B,2)):expected=True;break
 ok=(ga[3]==0)==expected
 print(json.dumps({'kind':typ,'n':n,'edges':sorted(G.edges()),'gamma':ga,'ehrhart':L,'ok':ok}),flush=True)
