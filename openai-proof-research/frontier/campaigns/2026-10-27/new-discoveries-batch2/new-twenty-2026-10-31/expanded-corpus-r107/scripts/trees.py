import pathlib,json,itertools,random,numpy as np
from scipy.optimize import linprog
D=pathlib.Path(__file__).resolve().parents[1];ps=list(itertools.permutations(range(4)));ix={p:i for i,p in enumerate(ps)};adj=[]
for p in ps:
 ns=[]
 for j in range(3):q=list(p);q[j],q[j+1]=q[j+1],q[j];ns.append(ix[tuple(q)])
 adj.append(ns)
rng=random.Random(107);cols=[];cert=[];results=[]
for batch in range(12):
 for trial in range(2000):
  # A single root branch: extreme rays suffice with tight ratios, truncated DFS or randomized growth.
  seen={0};par={};depth={0:0};front=[rng.choice(adj[0])];parent={front[0]:0};L=[8,12,16,20,23][trial%5]
  while front:
   j=rng.randrange(len(front)) if trial%3 else len(front)-1;v=front.pop(j)
   if v in seen:continue
   u=parent[v]
   if depth[u]>=L:continue
   seen.add(v);par[v]=u;depth[v]=depth[u]+1
   ns=[z for z in adj[v] if z not in seen];rng.shuffle(ns)
   for z in ns:
    if z in front:continue
    front.append(z);parent[z]=v
  w=np.array([2.**(-depth[v]) if v in seen else 0. for v in range(1,24)]);w/=sum(w);cols.append(w);cert.append(par)
 A=np.array(cols).T;r=linprog(np.ones(len(cols)),A_ub=-A,b_ub=-np.ones(23),bounds=(0,None),method='highs')
 row={'generated_trees':len(cols),'max_depths':[8,12,16,20,23],'status':r.status,'objective_sum_weight_over_min':float(r.fun) if r.success else None,'bound_diagnostic':int(r.fun)+1 if r.success else None}
 results.append(row);print(row,flush=True);(D/'outputs/trees.json').write_text(json.dumps(results,indent=2)+'\n')
 if r.success:
  active=np.flatnonzero(r.x>1e-9);(D/'outputs/tree-active.json').write_text(json.dumps([{'multiplier':float(r.x[j]),'parents':cert[j]} for j in active],indent=2)+'\n')
