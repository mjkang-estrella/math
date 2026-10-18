#!/usr/bin/env python3
"""Exact rational support diagnostics; not a proof of radial stability."""
from fractions import Fraction as Q
import json

def add(x,y):return tuple(a+b for a,b in zip(x,y))
def mul(c,x):return tuple(c*a for a in x)
def sub(x,y):return add(x,mul(-1,y))
def norm(x):return max(map(abs,x))
def contact(c,v):
    return min((1-(1 if z>0 else -1)*a)/abs(z) for a,z in zip(c,v) if z)
def support(z):
    j=max(range(2),key=lambda i:abs(z[i]));return lambda w:(1 if z[j]>=0 else -1)*w[j]
checks=0
for h in [Q(1,16),Q(1,8),Q(1,4)]:
    A=(Q(0),Q(1));B=(h,Q(1));eps=h;M=2*h
    def f(x):return B if x==A else A if x==B else x
    sphere=sorted(set([(Q(i,4),s) for i in range(-4,5) for s in [-1,1]]+[(s,Q(i,4)) for i in range(-4,5) for s in [-1,1]]+[A,B]))
    for x in sphere:
      for y in sphere:
        assert abs(norm(sub(f(x),f(y)))-norm(sub(x,y)))<=eps;checks+=1
    for t in [Q(1,4),Q(1,2),Q(3,4)]:
      a=1-t;U=1+t
      for y in sphere[::4]:
       b=f(y);c=mul(t,y);cb=mul(t,b)
       for x in [A,B]:
        p=norm(sub(x,c));v=mul(1/p,sub(x,c));s=norm(sub(f(x),cb));w=mul(1/s,sub(f(x),cb));u=contact(cb,mul(-1,w));z=f(sub(cb,mul(u,w)));r=norm(sub(c,z));g=mul(1/r,sub(c,z));D=s-p;delta=M-D
        assert delta>=0 and M-delta-eps<=r-u<=M
        Z=add(mul(p,v),mul(r,g));phi=support(Z)
        assert 0<=p+r-norm(Z)<=delta+eps
        assert p*(1-phi(v))+r*(1-phi(g))<=delta+eps
        checks+=3
        for l in sphere:
          pl=contact(c,l);xl=add(c,mul(pl,l));sl=norm(sub(f(xl),cb));eta=1-phi(l)
          assert sl-pl>=M-2*delta-3*eps-U*eta;checks+=1
# Sharp coefficient loss, including normalized averages.
for tau in [Q(1,n) for n in range(2,102)]:
    lam=tau/2;v1=(-1,1);v2=(1,1);avg=add(mul(lam,v1),mul(1-lam,v2))
    assert norm(avg)==1 and 1-avg[0]==tau and 1-v1[0]==tau/lam;checks+=1
print(json.dumps({'status':'PASS','exact_rational_checks':checks,'scope':'finite support/ray identities only; no invariant core or quantitative full theorem'},sort_keys=True))
