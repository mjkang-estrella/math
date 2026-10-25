from fractions import Fraction as Q
from pathlib import Path
R=Path('frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r244')
N=12
def add(a,b):return [a[i]+b[i] for i in range(N+1)]
def scale(a,c):return [c*x for x in a]
def deriv(a):return [(i+1)*a[i+1] if i<N else Q(0) for i in range(N+1)]
def mul(a,b):return [sum((a[j]*b[i-j] for j in range(i+1)),Q(0)) for i in range(N+1)]
def op(a):return add(deriv(deriv(a)),a)
def det(a,b):return add(mul(a[0],b[1]),scale(mul(a[1],b[0]),-1))
a=[Q(0)]*(N+1);a[0]=Q(1)
for n in range(N-1):a[n+2]=Q(n-1,(n+1)*(n+2))*a[n]
v=[Q(0)]*(N+1);v[1]=Q(1);h=[a,v];q=[scale(op(f),-1) for f in h];w=[scale(op(f),-1) for f in q]
cubic=add(scale(det([deriv(f) for f in h],w),Q(1,6)),scale(det([deriv(f) for f in q],q),Q(1,2)))
expect={0:Q(1,3),2:Q(-1,6),4:Q(-1,8),6:Q(-5,144)}
assert all(cubic[n]==z for n,z in expect.items())
assert w[0][0]/24==Q(-1,12)
assert scale(op(w[0]),-1)[0]/720==Q(1,90)
out='Exact rational recurrence checks (support only):\n'+str(expect)+'\nH1(0,t)=1-t^4/12+t^6/90+O(t^8).\nThe written general proof, not this finite series check, establishes (6.2).\n'
(R/'local-algebra.txt').write_text(out);print(out)
