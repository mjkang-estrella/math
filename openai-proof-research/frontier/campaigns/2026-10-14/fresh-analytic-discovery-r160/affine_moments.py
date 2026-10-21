"""Exact rational angular diagnostics; no universal theorem is inferred from tests."""
from fractions import Fraction as F
from math import prod
import json
from pathlib import Path
ROOT=Path('frontier/campaigns/2026-10-14/fresh-analytic-discovery-r160')
def add(*ps):
    out={}
    for p in ps:
        for k,v in p.items():out[k]=out.get(k,F(0))+v
    return {k:v for k,v in out.items() if v}
def scale(p,a):return {k:v*a for k,v in p.items() if v*a}
def mul(p,q):
    out={}
    for k,v in p.items():
        for l,w in q.items():
            m=tuple(a+b for a,b in zip(k,l));out[m]=out.get(m,F(0))+v*w
    return {k:v for k,v in out.items() if v}
def power(p,n):
    q={(0,0,0):F(1)}
    for _ in range(n):q=mul(q,p)
    return q
def der(p,i):
    out={}
    for k,v in p.items():
        if k[i]:
            l=list(k);l[i]-=1;out[tuple(l)]=v*k[i]
    return out
def oddfact(n):return prod(range(1,n+1,2))
def sphere(p):
    ans=F(0)
    for k,v in p.items():
        if any(a%2 for a in k):continue
        ans+=v*F(prod(oddfact(a-1) for a in k),oddfact(sum(k)+1))
    return ans # normalized surface measure
one={(0,0,0):F(1)};zero={}
x=[{tuple(int(i==j) for i in range(3)):F(1)} for j in range(3)]
Ax=[x[0],scale(x[1],-1),zero];q=add(power(x[0],2),scale(power(x[1],2),-1));v=[one,zero,zero]
T=[add(scale(add(v[i],scale(mul(x[0],x[i]),-1)),F(1,2)),scale(add(Ax[i],scale(mul(q,x[i]),-1)),F(1,3))) for i in range(3)]
H={2:add(power(x[0],2),scale(power(x[2],2),-1)),3:add(power(x[0],3),scale(mul(x[0],power(x[1],2)),-3)),4:add(power(x[0],4),scale(mul(power(x[0],2),power(x[1],2)),-6),power(x[1],4))}
out={}
for l,h in H.items():
    lap=add(*(der(der(h,i),i) for i in range(3)));assert not lap
    val=sphere(add(*(mul(mul(T[i],T[j]),der(der(h,i),j)) for i in range(3) for j in range(3))))
    assert val
    out[str(l)]={'test_harmonic':{str(k):str(v) for k,v in h.items()},'normalized_angular_moment':str(val)}
(ROOT/'notes/angular-diagnostics.json').write_text(json.dumps(out,indent=2))
print(json.dumps(out,indent=2))
