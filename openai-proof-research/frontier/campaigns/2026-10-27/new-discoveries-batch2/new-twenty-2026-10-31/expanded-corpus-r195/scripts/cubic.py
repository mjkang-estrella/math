import pathlib,json,random,itertools
import sys
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
from cubic_generator import nx
D=pathlib.Path(__file__).resolve().parents[1]
# Target Ahat: ab, ac twice, bc twice, ad, be.
stars=[sum(1<<e for e in es) for es in [[0,1,2,5],[0,3,4,6],[1,2,3,4]]]
def color(G,limit=200000):
 L=nx.line_graph(G);edges=list(L.edges());vs=list(L.nodes());idx={v:j for j,v in enumerate(vs)};E=[(idx[a],idx[b]) for a,b in edges];used=[0]*len(vs);assigned=[-1]*len(E);nodes=0
 def options(k):
  a,b=E[k];sa=[s for s in stars if s&used[a]==used[a]];sb=[s for s in stars if s&used[b]==used[b]]
  return [c for c in range(7) if not((used[a]|used[b])>>c&1) and any(s>>c&1 for s in sa) and any(s>>c&1 for s in sb)]
 def dfs(left):
  nonlocal nodes
  nodes+=1
  if nodes>limit:raise TimeoutError
  if not left:return True
  k=min(left,key=lambda z:len(options(z)));a,b=E[k]
  for c in options(k):
   assigned[k]=c;used[a]|=1<<c;used[b]|=1<<c
   if dfs(left-{k}):return True
   used[a]^=1<<c;used[b]^=1<<c;assigned[k]=-1
  return False
 try:r=dfs(set(range(len(E))))
 except TimeoutError:return 'limited',nodes
 if r:
  assert all(u in stars for u in used)
  assert all(assigned[a]!=assigned[b] for a in range(len(E)) for b in range(a) if set(E[a])&set(E[b]))
 return 'colorable' if r else 'failure',nodes
out=[]
for n in [4,8,12,16,20,24,28,32]:
 c={'n':n,'colorable':0,'limited':0,'failure':0,'attempted_seeds':80}
 for seed in range(80):
  G=nx.random_regular_graph(3,n,seed=195000+n*100+seed)
  if not nx.is_connected(G) or list(nx.bridges(G)):continue
  r,k=color(G,20000);c[r]+=1
  if r=='failure':c['edges']=list(G.edges());break
 out.append(c);print(c,flush=True)
 if c['failure']:break
(D/'outputs/cubic.json').write_text(json.dumps(out,indent=2))
