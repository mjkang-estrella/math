from math import gcd
import json
from pathlib import Path

d=182
roots=[u for u in range(d) if gcd(u,d)==1 and (u*u+3)%(2*d)==0]
rows=[]
for u in roots:
    H={((3*k)%(3*d),(u*k)%d) for k in range(d)}
    Hp={(a,b) for a in range(3*d) for b in range(d) if (a+u*b)%d==0}
    cosets=[{((a+j*d)%(3*d),b) for a,b in H} for j in range(3)]
    rows.append(dict(u=u,order_H=len(H),order_Hperp=len(Hp),isotropic=all((a*a+3*b*b)%(6*d)==0 for a,b in H),primitive_N=len({a for a,b in H})==d,primitive_T=len({b for a,b in H})==d,quotient_three=Hp==set.union(*cosets) and sum(map(len,cosets))==len(Hp)))
assert all(r['order_H']==d and r['order_Hperp']==3*d and all(r[k] for k in ['isotropic','primitive_N','primitive_T','quotient_three']) for r in rows)
# Independent changes of signs on N and T change u only to -u.
orbits=sorted({tuple(sorted({u,(-u)%d})) for u in roots})
# Finite incidence accounting: endpoint path S1->S2 can be balanced
# by an internal path S2->S1. Both row sums are zero.
incidence=[[-1,1],[1,-1]]
assert [sum(row) for row in incidence]==[0,0]
result=dict(d=d,threshold_claim=False,roots_mod_d=roots,sign_orbits=orbits,rows=rows,quotient_generator=[d,0],quotient_q_mod_2='2/3',two_path_incidence=incidence,interpretation='Finite quadratic-module and flow calculations only; no geometric birational-map construction.')
out=Path(__file__).parent/'private'/'finite-calculation.json'
out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
