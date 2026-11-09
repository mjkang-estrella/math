from pathlib import Path
import json,time
from sympy.polys.domains import GF
from sympy.polys.rings import ring
from sympy.polys.matrices import DomainMatrix
L=Path(__file__).resolve().parents[1]
p=1009;R,x=ring('x',GF(p));inv2=pow(2,-1,p)
# g(t)^2=(1+(1-x/2)t)(1+(1-x)t)(1+t), thesis (2.6), a=2,b=1
u=R.one-x*inv2;v=R.one-x
P=[R.one,u+v+1,u*v+u+v,u*v]
B=[R.one]
for k in range(1,27):B.append(( (P[k] if k<len(P) else R.zero)-sum((B[i]*B[k-i] for i in range(1,k)),R.zero))*inv2)
rows=[]
for n in range(3,25):
 m=(n-1)//2 if n%2 else n//2-1;shift=0 if n%2 else 1
 mat=[[B[i+j+2+shift] for j in range(m)] for i in range(m)]
 t=time.monotonic();d=DomainMatrix(mat,(m,m),R.to_domain()).det();g=d.gcd(d.diff(x));row={'n':n,'a':2,'b':1,'prime':p,'degree':d.degree(),'expected_degree':(n*n-1)//4 if n%2 else n*n//4-1,'gcd_derivative_degree':g.degree(),'squarefree':g.degree()==0,'seconds':time.monotonic()-t};rows.append(row);print(json.dumps(row),flush=True)
 (L/'outputs/billiard-check.json').write_text(json.dumps(rows,indent=2))
