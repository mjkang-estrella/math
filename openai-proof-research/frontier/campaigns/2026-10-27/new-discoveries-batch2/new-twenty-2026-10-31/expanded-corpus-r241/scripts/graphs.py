from pathlib import Path
import sys,json,random,itertools,time
D=Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'))
import networkx as nx
import z3
mode=sys.argv[1];rng=random.Random(241);counts={}
def packing(G):
 vs=list(G);s=z3.Solver();s.set(timeout=700);x={v:z3.Int('x'+str(v)) for v in vs}
 for v in vs:s.add(x[v]>=0,x[v]<4)
 for u in vs:
  for v,d in nx.single_source_shortest_path_length(G,u,cutoff=3).items():
   if u>=v:continue
   for c,r in enumerate([1,1,2,3]):
    if d<=r:s.add(z3.Or(x[u]!=c,x[v]!=c))
 return str(s.check())
def matching(G,M):
 n=len(G); es=list(G.edges()); mi={es.index(e) for e in es if e in M or e[::-1] in M}; xs=[z3.Bool('e'+str(i)) for i in range(len(es))];s=z3.Solver();s.set(timeout=1000)
 for mask in range(1,1<<(n-1)):
  cut=[(i, bool(mask>>u&1)) for i,(u,v) in enumerate(es) if bool(mask>>u&1)!=bool(mask>>v&1)]
  if len(cut)<3:return 'ineligible'
  if len(cut)==3 and sum(i in mi for i,b in cut)>1:return 'ineligible'
  out=[xs[i] if b else z3.Not(xs[i]) for i,b in cut]
  s.add(z3.Or(out),z3.Or([z3.Not(v) for v in out]))
  for k,(i,b) in enumerate(cut):
   if i in mi:s.add(z3.Or(z3.Not(out[k]),*[v for j,v in enumerate(out) if j!=k]),z3.Or(out[k],*[z3.Not(v) for j,v in enumerate(out) if j!=k]))
 return str(s.check())
if mode=='packing':
 graphs=[G for G in nx.graph_atlas_g() if len(G)>0 and nx.is_connected(G) and max(dict(G.degree()).values())<=3]
 graphs += [nx.random_regular_graph(3,n,seed=241000+n*100+j) for n in range(8,32,2) for j in range(50)]
else:
 graphs=[G for G in nx.graph_atlas_g() if len(G)>=4 and min(dict(G.degree()).values())>=3 and nx.is_connected(G)]
 graphs += [nx.random_regular_graph(3,n,seed=241000+n*100+j) for n in [8,10,12] for j in range(15)]
for idx,G in enumerate(graphs):
 if not nx.is_connected(G):continue
 if mode=='packing':
  if nx.is_isomorphic(G,nx.petersen_graph()):continue
  ans=packing(G);key=(len(G),ans);counts[str(key)]=counts.get(str(key),0)+1
  if ans=='unsat':print('WITNESS',nx.to_graph6_bytes(G,header=False).decode().strip(),flush=True)
 else:
  es=list(G.edges());ms=[]
  if len(G)<=6:
   for k in range(1,len(G)//2+1):
    ms += [list(m) for m in itertools.combinations(es,k) if len({v for e in m for v in e})==2*k]
  else:
   for j in range(3):
    rng.shuffle(es);used=set();m=[]
    for e in es:
     if not used.intersection(e):m.append(e);used.update(e)
    ms.append(m)
  for M in ms:
   ans=matching(G,M);key=(len(G),ans);counts[str(key)]=counts.get(str(key),0)+1
   if ans=='unsat':print('WITNESS',nx.to_graph6_bytes(G,header=False).decode().strip(),M,flush=True)
 if idx%10==0:print(idx,counts,flush=True)
print('COMPLETE',len(graphs),counts,flush=True)
