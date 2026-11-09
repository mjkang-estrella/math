from pathlib import Path
from fractions import Fraction as F
import json,numpy as np
from scipy.optimize import linprog,linear_sum_assignment
from scipy.sparse import coo_matrix
L=Path(__file__).parent;N=200;S=40000
slopes=[[10,13,22,28,29],[5,9,9,16,18]]
def q(k,u):
 j=min(int(5*u),4)
 return sum(F(s,50) for s in slopes[k][:j])+F(slopes[k][j],10)*(u-F(j,5))
hx=[F(159*i,1000) for i in range(21)];sign=[-1,-1,1,1,1,-1,-1,-1,-1,-1,1,1,-1,-1,-1,-1,-1,-1,-1,1]
hy=[F(0)]
for s in sign:hy.append(hy[-1]+s*F(159,1000))
def h(x):
 j=min(int(x/F(159,1000)),19)
 return hy[j]+sign[j]*(x-hx[j])
u=[F(2*i+1,2*N) for i in range(N)];a=[q(0,x) for x in u];b=[q(1,x) for x in u];r=[(x+y)/2 for x,y in zip(a,b)]
C=np.array([[float(h(x+y)) for y in b] for x in a]);_,perm=linear_sum_assignment(C,maximize=True)
old=sum(h(a[i]+b[j]) for i,j in enumerate(perm))/N
cost=[[h(x+y) for y in r] for x in r]
ii,jj=np.triu_indices(N);rows=np.repeat(np.arange(len(ii)),2);cols=np.column_stack([ii,jj]).ravel()
A=coo_matrix((-np.ones(len(rows)),(rows,cols)),shape=(len(ii),N)).tocsr()
res=linprog(np.full(N,2/N),A_ub=A,b_ub=-np.array([float(cost[i][j]) for i,j in zip(ii,jj)]),bounds=[(None,None)]*N,method='highs',options={'threads':1})
assert res.success
dual=[F(int(np.ceil(x*S)),S) for x in res.x]
assert all(dual[i]+dual[j]>=cost[i][j] for i in range(N) for j in range(N))
upper=2*sum(dual)/N
# conservative total midpoint error for both source and target <= (29/10+18/10)/N.
error=F(47,10*N);gap=old-upper-error
out=dict(N=N,scale=S,slopes_tenths=slopes,hx=list(map(str,hx)),hy=list(map(str,hy)),old_permutation=perm.tolist(),dual=list(map(str,dual)),old_midpoint_value=str(old),new_midpoint_upper=str(upper),total_error_bound=str(error),certified_gap=str(gap),positive=gap>0)
(L/'certificate.json').write_text(json.dumps(out,indent=2));print({k:v for k,v in out.items() if k not in ['dual','old_permutation','hx','hy']})
