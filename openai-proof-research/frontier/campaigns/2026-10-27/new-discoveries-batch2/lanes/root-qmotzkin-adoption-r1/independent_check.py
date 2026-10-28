import json
from pathlib import Path
import sympy as s
q=s.Symbol("q")
mu=[s.Integer(1)]
for n in range(12):
 mu.append(s.expand(mu[n]+sum(q**(r+1)*mu[r]*mu[n-1-r] for r in range(n))))
beta=lambda n:n*(n-1)*(2*n-1)//6
N=12
B=s.Matrix(N,N,lambda i,j:q**j if abs(i-j)<=1 else 0)
checks=[]
for n in range(1,5):
 direct=s.Matrix(n,n,lambda i,j:mu[i+j+2]).det(method="domain-ge")
 closed=q**(beta(n+1)-1)*(1+q)+sum(q**(beta(n+1)-j) for j in range(2,n+1) if j%3!=2)
 checks.append((f"shift2_n{n}",s.expand(direct-closed)==0))
 for r in range(6):
  H=s.Matrix(n,n,lambda i,j:mu[i+j+r])
  power=B**r
  checks.append((f"block_n{n}_r{r}",s.expand(H.det(method="domain-ge")-q**beta(n)*power[:n,:n].det(method="domain-ge"))==0))
T=B**2*s.diag(*[q**(-i) for i in range(N)])
minor=s.expand(T.extract([0,1,2],[0,1,3]).det(method="domain-ge"))
result={"checks":checks,"passed":sum(ok for _,ok in checks),"total":len(checks),"T_minor_k2_n3_013":str(minor),"scope":"bounded independent diagnostics only"}
Path(__file__).with_name("independent-checks.json").write_text(json.dumps(result,indent=2)+"\n")
assert all(ok for _,ok in checks)
print(json.dumps({k:v for k,v in result.items() if k!="checks"}))
