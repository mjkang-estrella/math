from pathlib import Path
import sys,random,time
D=Path(__file__).resolve().parents[1];sys.path.insert(0,str(D.parent/'expanded-corpus-r58/deps'))
import networkx as nx,z3
rng=random.Random(2411);counts={}
for n in [14,16,20,24,30,40,50,60]:
 for j in range(30):
  G=nx.random_regular_graph(3,n,seed=241000+n*100+j)
  if not nx.is_connected(G) or nx.edge_connectivity(G)<3:continue
  es=list(G.edges());xs=[z3.Bool('x'+str(i)) for i in range(len(es))];rng.shuffle(es);used=set();M=[]
  for i,(u,v) in enumerate(es):
   if u not in used and v not in used:M.append(i);used.update([u,v])
  # Certify eligibility by absence of 3-cuts containing any pair of M.
  eligible=True
  for a,b in __import__('itertools').combinations(M,2):
   H=G.copy();H.remove_edges_from([es[a],es[b]])
   if list(nx.bridges(H)):eligible=False;break
  if not eligible:counts['ineligible']=counts.get('ineligible',0)+1;continue
  s=z3.Solver();s.set(timeout=800);start=time.monotonic();rounds=0;answer='unknown'
  while time.monotonic()-start<2:
   r=s.check()
   if r!=z3.sat:answer=str(r);break
   model=s.model();edges=[(u,v) if z3.is_true(model.eval(xs[i],model_completion=True)) else (v,u) for i,(u,v) in enumerate(es)];bad=[]
   for deleted in [-1]+M:
    H=nx.DiGraph();H.add_nodes_from(G);H.add_edges_from(e for i,e in enumerate(edges) if i!=deleted)
    if not nx.is_strongly_connected(H):bad.extend(set(C) for C in nx.strongly_connected_components(H))
   if not bad:answer='sat';break
   for C in bad:
    for deletion in [-1]+M:
     out=[]
     for i,(u,v) in enumerate(es):
      if i==deletion:continue
      if u in C and v not in C:out.append(xs[i])
      if v in C and u not in C:out.append(z3.Not(xs[i]))
     s.add(z3.Or(out))
   rounds+=1
  counts[answer]=counts.get(answer,0)+1
  if answer=='unsat':print('WITNESS',nx.to_graph6_bytes(G,header=False).decode().strip(),[es[i] for i in M],flush=True)
  print('CASE',n,j,answer,'rounds',rounds,flush=True)
 print('ROW',n,counts,flush=True)
print('COMPLETE',counts,flush=True)
