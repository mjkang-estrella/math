import networkx as nx,random,pathlib,json,time
from fractions import Fraction
from functools import lru_cache
D=pathlib.Path(__file__).resolve().parents[1];random.seed(375345);rows=[];start=time.monotonic()
def test(G,kind):
 G=nx.convert_node_labels_to_integers(G);n=len(G);adj=[sum(1<<v for v in G[u]) for u in range(n)]
 @lru_cache(None)
 def f(S):
  for u in range(n):
   if S>>u&1 and adj[u]&S:break
  else:return 0
  v=((adj[u]&S)&-(adj[u]&S)).bit_length()-1
  options=[]
  for a in (u,v):
   B=adj[a]&S
   while B:
    bit=B&-B;b=bit.bit_length()-1;B^=bit
    options.append(1+f(S&~(1<<a)&~bit))
  return min(options)
 sat=f((1<<n)-1);H=sum((Fraction(2,G.degree(u)+G.degree(v)) for u,v in G.edges()),Fraction())
 r=dict(n=n,kind=kind,saturation=sat,harmonic=str(H),gap=str(H-sat),counterexample=sat>H)
 if sat>H:r['edges']=list(G.edges())
 rows.append(r)
 if sat>H:print('COUNTEREXAMPLE',r,flush=True)
 if len(rows)%50==0:
  print('tested',len(rows),n,flush=True);(D/'outputs/harmonic.json').write_text(json.dumps(rows,indent=2)+'\n')
for n in range(12,29):
 for j in range(70):
  # start tree, add random edges maintaining degree <=4
  G=nx.random_labeled_tree(n,seed=random.randrange(1<<30))
  if max(dict(G.degree()).values())>4:continue
  pairs=list(nx.non_edges(G));random.shuffle(pairs)
  for u,v in pairs[:random.randrange(len(pairs)+1)]:
   if G.degree(u)<4 and G.degree(v)<4:G.add_edge(u,v)
  test(G,'seeded degree-capped tree plus edges')
  if time.monotonic()-start>95:break
 if time.monotonic()-start>95:break
(D/'outputs/harmonic.json').write_text(json.dumps(rows,indent=2)+'\n');print('TOTAL',len(rows),flush=True)
