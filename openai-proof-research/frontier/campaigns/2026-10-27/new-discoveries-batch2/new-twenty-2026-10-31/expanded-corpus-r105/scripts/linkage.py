import itertools,pathlib,json,numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
from scipy.sparse import lil_matrix
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for v,w in [(5,3),(6,4)]:
 S=set()
 for a,b,c in itertools.combinations(range(1,2**v),3):
  s=frozenset([a,b,c,a^b,a^c,b^c,a^b^c])
  if len(s)==7 and 0 not in s and sum(x<2**w for x in s)>=3:S.add(s)
 S=list(S);pairs=[(i,j) for i in range(len(S)) for j in range(i) if len(S[i]&S[j])>=3];A=lil_matrix((len(pairs),len(S)))
 for t,(i,j) in enumerate(pairs):A[t,i]=A[t,j]=1
 res=milp(-np.ones(len(S)),integrality=np.ones(len(S)),bounds=Bounds(0,1),constraints=LinearConstraint(A.tocsr(),-np.inf,1),options={'time_limit':90,'threads':2})
 selected=[sorted(S[i]) for i,x in enumerate(res.x) if x>.5] if res.x is not None else []
 z=dict(v1=v,v2=w,q=2,k=3,d=4,eligible_subspaces=len(S),conflict_pairs=len(pairs),status=int(res.status),message=res.message,lower=len(selected),upper=float(-res.mip_dual_bound),selected=selected);out.append(z);print({k:v for k,v in z.items() if k!='selected'},flush=True);(D/'outputs/linkage.json').write_text(json.dumps(out,indent=2))
