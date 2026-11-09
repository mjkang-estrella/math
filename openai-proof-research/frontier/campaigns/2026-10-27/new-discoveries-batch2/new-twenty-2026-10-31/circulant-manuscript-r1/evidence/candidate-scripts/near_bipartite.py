import itertools,random,numpy as np,json,pathlib
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(108)
def packing(n,E):
 es=sorted(E);idx={e:i for i,e in enumerate(es)};tri=[t for t in itertools.combinations(range(n),3) if all(e in E for e in itertools.combinations(t,2))]
 if not tri:return 0
 rows=[];cols=[]
 for j,t in enumerate(tri):
  for e in itertools.combinations(t,2):rows.append(idx[e]);cols.append(j)
 M=coo_matrix((np.ones(len(rows)),(rows,cols)),shape=(len(es),len(tri))).tocsr()
 r=linprog(-np.ones(len(tri)),A_ub=M,b_ub=np.ones(len(es)),bounds=(0,None),method='highs');assert r.success
 return -3*r.fun
out=[]
for n in [26,27,28,32,40]:
 allE=set(itertools.combinations(range(n),2));k=n//2;cross={e for e in allE if e[0]<k<=e[1]};inside=allE-cross
 for trial in range(40):
  add=rng.randrange(n//8+1,n//8+9);delete=rng.randrange(41);E=(cross-set(rng.sample(sorted(cross),delete)))|set(rng.sample(sorted(inside),add))
  val=packing(n,E)+packing(n,allE-E);eta=val/(n*(n-1));row=dict(n=n,trial=trial,added=add,deleted=delete,nu_sum=val,eta=eta)
  if eta<=.25000001:row['edges']=sorted(E)
  out.append(row)
 print(n,min(r['eta'] for r in out if r['n']==n),flush=True);(D/'outputs/near-bipartite.json').write_text(json.dumps(out,indent=2))
