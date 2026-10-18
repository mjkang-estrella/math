#!/usr/bin/env python3
"""Finite checks of route exclusions; not proof. Original code MIT."""
from fractions import Fraction as F
from itertools import combinations_with_replacement
from decimal import Decimal as D, localcontext
import json

out={'path_checks':[],'entropy_checks':[],'normalization_checks':[]}
for m in range(1,6):
    n=2*m+1;t=F(1,3);x=[F(0)]*m+[t]+[F(1)]*m
    grid=[F(0),F(1,3),F(2,3),F(1),F(4,3)]
    best=None;minimizers=[];count=0
    for rev in combinations_with_replacement(grid,n):
        q=tuple(reversed(rev));v=sum(abs(a-b) for a,b in zip(q,x));count+=1
        if best is None or v<best:best=v;minimizers=[q]
        elif v==best:minimizers.append(q)
    assert best==m and minimizers==[(t,)*n]
    out['path_checks'].append({'n':n,'grid_candidates':count,'unique_grid_minimizer':'constant1/3','minimum':str(best),'exact_ratio':n})
with localcontext() as ctx:
    ctx.prec=70
    for denominator in [2,4,8,16,32,64]:
        e=D(1)/denominator;a=e*e;delta=a/D(10)**8
        def f(l):return (1+a)*l.exp()-(-l).exp()-(a+delta)*(-l/e).exp()
        lo=D(0);hi=delta
        assert f(lo)<0<f(hi)
        for _ in range(220):
            mid=(lo+hi)/2
            if f(mid)>0:hi=mid
            else:lo=mid
        l=(lo+hi)/2;r=(1+a)*l.exp();z=(-l).exp();s=(a+delta)*(-l/e).exp()
        assert abs(r-z-s)<D('1e-60')
        # Actual positive gradient is lambda*(1,-1,-1), dual to the cone.
        assert r>1+a and z<1 and s>a
        ratio=((r-1-a)+(1-z)+e*(s-a))/(e*delta)
        exact=F(1)+F(2)/(F(1,denominator)*(2+F(1,denominator**2)+F(1,denominator)))
        predicted=D(exact.numerator)/D(exact.denominator)
        assert abs(ratio-predicted)/predicted<D('1e-7')
        out['entropy_checks'].append({'epsilon':'1/'+str(denominator),'derivative_ratio_exact':str(exact),'finite_difference_ratio':str(ratio),'tolerance_relative':'1e-7'})
for denominator in [10,100,1000]:
    h=F(1);eta=F(1,denominator);c=(h-eta)/(3*h)
    value=h*abs(2*c-1)+h*c
    assert value==(2*h+eta)/3
    out['normalization_checks'].append({'eta':str(eta),'exact_output_input_ratio':str(value/eta)})
out['status']='PASS_FINITE_DIAGNOSTICS_NOT_PROOF'
print(json.dumps(out,indent=2))
