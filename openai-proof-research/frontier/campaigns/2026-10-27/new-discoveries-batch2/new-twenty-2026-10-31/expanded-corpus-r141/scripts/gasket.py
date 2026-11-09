import itertools,json
out=[]
graphs=[]
for n in range(1,6):
 es=list(itertools.combinations(range(n),2))
 for mask in range(1<<len(es)):graphs.append((n,[e for i,e in enumerate(es) if mask>>i&1]))
for idx,(n,edges) in enumerate(graphs):
 if not n:continue
 k=0;col=None
 for k in range(1,n+1):
  # symmetry break: first vertex 0
  col=next((c for c in itertools.product(range(k),repeat=n) if c[0]==0 and all(c[u]!=c[v] for u,v in edges)),None)
  if col is not None:break
 for t in range(2,5 if n>4 else 6):
  weights=[2**(t-h-2) if h<t-1 else 1 for h in range(t)]
  assert all(weights[h]==sum(weights[h+1:]) for h in range(t-1))
  colors={w:sum(a*col[x] for a,x in zip(weights,w))%k for w in itertools.product(range(n),repeat=t)}
  checks=0
  # surviving base-copy edges
  for pre in itertools.product(range(n),repeat=t-1):
   for u,v in edges:assert colors[pre+(u,)]!=colors[pre+(v,)];checks+=1
  # all literal linking-edge identifications
  contractions=0
  for h in range(t-1):
   for pre in itertools.product(range(n),repeat=h):
    for u,v in edges:
     a=pre+(u,)+(v,)*(t-h-1);b=pre+(v,)+(u,)*(t-h-1)
     assert colors[a]==colors[b];contractions+=1
  out.append(dict(atlas=idx,n=n,t=t,k=k,vertices=n**t,base_edge_checks=checks,link_checks=contractions))
print(json.dumps({'instances':len(out),'word_vertices':sum(r['vertices'] for r in out),'base_edge_checks':sum(r['base_edge_checks'] for r in out),'link_checks':sum(r['link_checks'] for r in out)}))
json.dump(out,open('outputs/gasket.json','w'),indent=2)
