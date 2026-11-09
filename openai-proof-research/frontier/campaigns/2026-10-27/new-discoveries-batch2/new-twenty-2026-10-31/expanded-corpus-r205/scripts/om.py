import itertools,random,json,pathlib
import sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
import graphlib_local as nx
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(205)
def det(a,b,c):return a[0]*(b[1]*c[2]-b[2]*c[1])-a[1]*(b[0]*c[2]-b[2]*c[0])+a[2]*(b[0]*c[1]-b[1]*c[0])
out=[]
for n in [5,6,7]:
 for trial in range(12):
  while True:
   pts=[(rng.randrange(-9,10),rng.randrange(-9,10),1) for _ in range(n)]
   if all(det(*[pts[i] for i in ids])!=0 for ids in itertools.combinations(range(n),3)):break
  circuits=[]
  for ids in itertools.combinations(range(n),4):
   coeff=[(-1)**j*det(*[pts[i] for z,i in enumerate(ids) if z!=j]) for j in range(4)]
   p=sum(1<<i for i,c in zip(ids,coeff) if c>0);q=sum(1<<i for i,c in zip(ids,coeff) if c<0);circuits.extend([(p,q),(q,p)])
  M=nx.Graph();M.add_nodes_from(range(1<<n));G=nx.Graph();G.add_nodes_from(range(1<<n))
  for a,b in itertools.combinations(range(1<<n),2):
   x=a&~b;y=b&~a
   if (x,y) in circuits:M.add_edge(a,b)
   if not any(p&x==p and q&y==q for p,q in circuits):G.add_edge(a,b)
  comps=list(nx.connected_components(M));nontriv=[c for c in comps if len(c)>1];univ=[v for v in G if G.degree(v)==len(G)-1];core=G.subgraph(set(G)-set(univ))
  cliques=list(nx.find_cliques(core));omega=max(map(len,cliques),default=0)+len(univ)
  local=[max((len(c) for c in nx.find_cliques(G.subgraph(C))),default=0) for C in nontriv]
  maxima=[set(c)|set(univ) for c in cliques if len(c)+len(univ)==omega];bad=[{'S':sorted(S),'component':sorted(C),'local_max':l} for S in maxima for C,l in zip(nontriv,local) if len(S&C)!=l]
  r={'n':n,'trial':trial,'points':pts,'circuits':circuits,'maximum':omega,'expected_independent_sets':1+n+n*(n-1)//2+n*(n-1)*(n-2)//6,'maxima_count':len(maxima),'nontrivial_components':[len(C) for C in nontriv],'bad':bad[:1]};out.append(r);print(json.dumps(r),flush=True)
  if bad:break
(D/'outputs/om.json').write_text(json.dumps(out,indent=2))
