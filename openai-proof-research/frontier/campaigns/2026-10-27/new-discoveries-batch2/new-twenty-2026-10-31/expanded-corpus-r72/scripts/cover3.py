import pathlib,json,itertools,numpy as np,time,random,warnings
from scipy.optimize import linprog,milp,Bounds,LinearConstraint
warnings.filterwarnings('ignore');D=pathlib.Path(__file__).resolve().parents[1];rng=random.Random(377831);P=list(itertools.product(range(3),repeat=3));pairs=list(itertools.product(range(3),repeat=2));A=np.array([[int(all(p[i]==v for i,v in zip([j for j in range(3) if j!=ax],ab))) for p in P] for ax in range(3) for ab in pairs]);records=[];start=time.monotonic()
for t in range(300):
 if time.monotonic()-start>95:break
 density=[.4,.5,.6,.7,.8,.9][t%6];H=[rng.random()<density for p in P]
 res=linprog(np.zeros(27),A_eq=A,b_eq=np.ones(27),bounds=[(0,None) if h else (0,0) for h in H],method='highs',options={'threads':1})
 if res.success:records.append(dict(t=t,H=''.join(map(str,map(int,H))),uniform_feasible=True));continue
 C=milp(np.ones(27),integrality=np.ones(27),bounds=Bounds(0,1),constraints=LinearConstraint(A.T[H],1,np.inf),options={'threads':1,'time_limit':1})
 rec=dict(t=t,H=''.join(map(str,map(int,H))),uniform_feasible=False,cover_objective=C.fun,cover_lower=getattr(C,'mip_dual_bound',None));
 if C.fun is not None and C.fun>8.5 and C.mip_dual_bound>8.5:
  feasible=[]
  for r in itertools.product(range(1,5),repeat=3):
   if __import__('math').gcd(*r)>1:continue
   b=np.array([r[i]*r[j] for ax in range(3) for i,j in pairs]);R=linprog(np.zeros(27),A_eq=A,b_eq=b,bounds=[(0,None) if h else (0,0) for h in H],method='highs',options={'threads':1})
   if R.success:feasible=list(r);break
  rec['tested_class_sizes_max4_first_feasible']=feasible
 records.append(rec)
out=dict(seed=377831,full_S=True,trials=len(records),records=records,seconds=time.monotonic()-start,note='floating LP/MILP diagnostics, not a full converse proof or certified infeasibility for all positive class sizes');(D/'outputs/cover3.json').write_text(json.dumps(out,indent=2));print(out)
