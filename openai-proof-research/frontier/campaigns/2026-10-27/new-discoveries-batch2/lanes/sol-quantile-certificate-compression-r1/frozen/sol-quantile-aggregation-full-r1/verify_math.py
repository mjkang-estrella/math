"""Exact checker; standard library only, no optimizer or numerical tolerances."""
from pathlib import Path
from fractions import Fraction as F
import json
L=Path(__file__).parent
c=json.loads((L/'certificate.json').read_text());N=c['N']
assert N==200
slopes=[[F(v,10) for v in row] for row in c['slopes_tenths']]
assert slopes==[[F(1),F(13,10),F(22,10),F(28,10),F(29,10)],[F(5,10),F(9,10),F(9,10),F(16,10),F(18,10)]]
assert all(0<row[0] and all(x<=y for x,y in zip(row,row[1:])) for row in slopes)
def q(k,u):
 j=min(int(5*u),4)
 return sum(slopes[k][:j],F(0))/5+slopes[k][j]*(u-F(j,5))
hx=list(map(F,c['hx']));hy=list(map(F,c['hy']))
assert hx==[F(159*i,1000) for i in range(21)]
sign=[(hy[i+1]-hy[i])/(hx[i+1]-hx[i]) for i in range(20)]
assert all(abs(s)==1 for s in sign)
def h(x):
 assert 0<=x<=hx[-1]
 j=min(int(x/F(159,1000)),19)
 return hy[j]+sign[j]*(x-hx[j])
u=[F(2*i+1,2*N) for i in range(N)]
a=[q(0,x) for x in u];b=[q(1,x) for x in u];r=[(x+y)/2 for x,y in zip(a,b)]
p=c['old_permutation'];assert sorted(p)==list(range(N))
old=sum((h(a[i]+b[p[i]]) for i in range(N)),F(0))/N
d=list(map(F,c['dual']));assert len(d)==N
for i in range(N):
 for j in range(N):assert d[i]+d[j]>=h(r[i]+r[j])
upper=2*sum(d,F(0))/N
error=(slopes[0][-1]+slopes[1][-1])/N
gap=old-upper-error
assert str(old)==c['old_midpoint_value'] and str(upper)==c['new_midpoint_upper']
assert str(error)==c['total_error_bound'] and str(gap)==c['certified_gap'] and gap>0
out=dict(status='PASS',dual_inequalities=N*N,permutation_verified=True,decreasing_densities=True,old_midpoint=str(old),new_midpoint_upper=str(upper),continuous_total_error=str(error),strict_continuous_gap=str(gap),uses_floating_point=False)
(L/'math-verification.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
