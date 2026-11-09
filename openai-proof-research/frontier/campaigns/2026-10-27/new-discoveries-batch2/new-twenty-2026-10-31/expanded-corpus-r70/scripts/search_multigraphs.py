import itertools,json,pathlib,networkx as nx
D=pathlib.Path(__file__).resolve().parents[1];rows=[];bad=[]
def ec(es,k):
 used=[set() for _ in range(4)]
 def go(j):
  if j==len(es):return True
  u,v=es[j]
  for c in range(k):
   if c not in used[u] and c not in used[v]:
    used[u].add(c);used[v].add(c)
    if go(j+1):return True
    used[u].remove(c);used[v].remove(c)
  return False
 return go(0)
for n in range(2,5):
 pairs=list(itertools.combinations(range(n),2));count=crit=den=0
 for mult in itertools.product(range(3),repeat=len(pairs)):
  es=[e for e,m in zip(pairs,mult) for _ in range(m)];G=nx.Graph();G.add_nodes_from(range(n));G.add_edges_from(es)
  if not nx.is_connected(G):continue
  count+=1;degrees=[sum(v in e for e in es) for v in range(n)];Delta=max(degrees)
  gamma=max((sum(u in S and v in S for u,v in es)+(len(S)//2)-1)//(len(S)//2) for s in range(2,n+1) for S in map(set,itertools.combinations(range(n),s)))
  colored=ec(es,Delta)
  if gamma<=Delta-1:
   den+=1
   if not colored:bad.append(dict(id=375252,edges=es))
  if not colored and ec(es,Delta+1) and all(ec(es[:i]+es[i+1:],Delta) for i in range(len(es))):
   crit+=1
   if 6*len(es)<n*(2*Delta+2):bad.append(dict(id=375251,edges=es))
 rows.append(dict(n=n,multiplicities='0..2',connected_labeled=count,critical=crit,density_eligible=den))
(D/'outputs/multigraphs.json').write_text(json.dumps(dict(coverage=rows,counterexamples=bad),indent=2)+'\n');print(rows,bad)
