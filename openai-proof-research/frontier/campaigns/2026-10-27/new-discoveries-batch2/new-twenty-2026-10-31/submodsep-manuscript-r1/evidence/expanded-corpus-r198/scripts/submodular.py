import pathlib,json,itertools,numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for d,r in [(2,2),(3,2),(3,3),(4,2)]:
 # empty monomial always 1: restriction to that face is necessary
 coords=[s for k in range(1,r+1) for s in itertools.combinations(range(d),k)];n=len(coords);N=1<<n
 fam={sum((all(x>>a&1 for a in s))<<j for j,s in enumerate(coords)) for x in range(1<<d)}
 row=[];col=[];val=[];c=0
 for i in range(n):
  for j in range(i+1,n):
   for x in range(N):
    if x&(1<<i|1<<j):continue
    for a,b in [(x,1),(x|1<<i|1<<j,1),(x|1<<i,-1),(x|1<<j,-1)]:row.append(c);col.append(a);val.append(b)
    c+=1
 A=coo_matrix((val,(row,col)),shape=(c,N)).tocsr()
 z=linprog(np.zeros(N),A_ub=A,b_ub=np.zeros(c),bounds=[(None,-1) if x in fam else (0,None) for x in range(N)],method='highs',options={'time_limit':60})
 a={'d':d,'r':r,'coordinates_without_empty':n,'variables':N,'inequalities':c,'status':z.status,'message':z.message}
 if z.success:
  rounded=np.rint(z.x);a['integral_solution']=bool(np.max(abs(z.x-rounded))<1e-6);a['min_value']=float(min(z.x));a['max_value']=float(max(z.x));np.save(D/'outputs'/f'submod-{d}-{r}.npy',z.x)
 out.append(a);print(a,flush=True)
 (D/'outputs/submodular-search.json').write_text(json.dumps(out,indent=2))
