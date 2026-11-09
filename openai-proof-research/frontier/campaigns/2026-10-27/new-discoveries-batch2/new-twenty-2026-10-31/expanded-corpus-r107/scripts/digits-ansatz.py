import pathlib,json,numpy as np
from scipy.optimize import linprog
from fractions import Fraction
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for p in [13,17,29,37,41,53,61,73,89,97,101,109,113,137,149,157,173,181,193,197,229,257,401]:
 ds=list(range((p+1)//2))+[(p+3)//2];ss=set(ds);special=ds[-1]
 aps=[[(a+k*b)%p for k in range(4)] for a in ds for b in range(1,p) if all((a+k*b)%p in ss for k in range(4))]
 for degree in [2,3,4]:
  def basis(t):return [t**k for k in range(1,degree+1)]+[int(t==special),(-1)**t,t*(-1)**t]
  rows=np.array([[sum(s*basis(ap[i])[k] for i,s in enumerate([1,-1,-1,1])) for k in range(degree+3)] for ap in aps],dtype=float)
  r=linprog(np.zeros(degree+3),A_ub=-rows,b_ub=-np.ones(len(aps)),bounds=(None,None),method='highs')
  y=[Fraction(float(v)).limit_denominator(1000000) for v in r.x] if r.success else []
  margin=min(sum(int(v)*z for v,z in zip(row,y)) for row in rows) if y else None
  row={'p':p,'degree':degree,'LP_status':r.status,'coefficients':[str(v) for v in y],'exact_positive_margin':margin is not None and margin>0};out.append(row);print(row,flush=True)
  if y:break
(D/'outputs/digits-ansatz.json').write_text(json.dumps(out,indent=2)+'\n')
