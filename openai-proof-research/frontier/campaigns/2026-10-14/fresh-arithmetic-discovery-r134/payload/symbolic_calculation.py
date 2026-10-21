# Exact Laurent-polynomial checks; no numerical or categorical proof claim.
from fractions import Fraction as F
import json
def add(*polys):
    r={}
    for p in polys:
        for e,c in p.items(): r[e]=r.get(e,F(0))+c
    return {e:c for e,c in r.items() if c}
def scale(p,a): return {e:c*a for e,c in p.items() if c*a}
def mul(a,b):
    r={}
    for e,c in a.items():
        for f,d in b.items():
            k=tuple(x+y for x,y in zip(e,f));r[k]=r.get(k,F(0))+c*d
    return {e:c for e,c in r.items() if c}
one={(0,0,0):F(1)};m={(1,0,0):F(1)};n={(0,1,0):F(1)}
t={(0,0,1):F(1)};ti={(0,0,-1):F(1)}
def h(x,k,ki):return scale(mul(ki,add(mul(x,x),scale(mul(add(one,scale(k,-1)),x),2))),F(1,4))
nu=add(m,scale(mul(t,n),-1))
nud=add(n,scale(mul(ti,m),-1))
A=add(scale(m,-1),scale(one,-2),scale(mul(t,n),-1))
B=add(m,mul(t,add(n,scale(one,2))))
N=mul(add(m,one),add(n,one))
expected=add(scale(mul(ti,mul(m,add(m,scale(one,2)))),F(1,4)),scale(mul(t,mul(n,add(n,scale(one,2)))),F(1,4)),scale(add(mul(m,n),m,n),F(-1,2)))
ell=add(m,one)
radial=add(ell,scale(one,-1),scale(mul(mul(ell,nu),ti),-1),mul(mul(ell,add(ell,scale(one,-1))),ti))
identities={
'dual_charge':add(nu,mul(t,nud)),
'highest_weight_formula':add(h(nu,t,ti),scale(expected,-1)),
'dual_highest_weight':add(h(nu,t,ti),scale(h(nud,ti,t),-1)),
'outgoing_A_gap':add(h(A,t,ti),scale(h(nu,t,ti),-1),scale(N,-1)),
'outgoing_B_gap':add(h(B,t,ti),scale(h(nu,t,ti),-1),scale(N,-1)),
'full_cluster_exponent':add(radial,scale(N,-1),one)
}
assert all(not p for p in identities.values())
print(json.dumps({'kind':'exact polynomial bookkeeping only','identically_zero':list(identities)},indent=2))
