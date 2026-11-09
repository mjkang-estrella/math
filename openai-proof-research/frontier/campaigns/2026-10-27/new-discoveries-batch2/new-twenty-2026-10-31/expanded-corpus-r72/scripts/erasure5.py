import itertools,pathlib,json,numpy as np
from scipy.optimize import milp,Bounds,LinearConstraint
D=pathlib.Path(__file__).resolve().parents[1];r=5;m=4;cs=set();mat=0
for cols in itertools.combinations(range(1,2**r),m):
 span={0}
 for c in cols:span|={v^c for v in list(span)}
 if len(span)!=16:continue
 mat+=1;cs.add(sum(1<<(a-1) for a in range(1,32) if sum((a&c).bit_count()%2 for c in cols)==1))
A=np.array([[(mask>>i)&1 for i in range(31)] for mask in cs],float);res=milp(np.ones(31),integrality=np.ones(31),bounds=Bounds(0,1),constraints=LinearConstraint(A,1,np.inf),options={'time_limit':95,'threads':1});out=dict(r=r,unordered_rank4_column_sets=mat,distinct_constraints=len(cs),status=res.message,objective=res.fun,lower_bound=getattr(res,'mip_dual_bound',None),gap=getattr(res,'mip_gap',None),witness=[i+1 for i in range(31) if res.x is not None and res.x[i]>.5]);(D/'outputs/erasure5.json').write_text(json.dumps(out,indent=2));print(out)
