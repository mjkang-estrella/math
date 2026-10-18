#!/usr/bin/env python3
# MIT. Finite arithmetic diagnostics only; not a proof.
import math,json

def coeff(p):
    e=p*math.sqrt(p*p+2);alpha=(p*p+1)/e
    return e,alpha,(alpha-1)/2

for p in [0.01,0.1,1,3]:
    e,a,v2=coeff(p)
    assert math.isclose(e*e*(a*a-1),1,rel_tol=1e-11)
    assert math.isclose(e*a-1,p*p,rel_tol=1e-10,abs_tol=1e-14)
    ell=.1*p*p
    assert math.isclose((e-a*ell)**2-ell*ell*(a*a-1),e*e-2*e*a*ell+ell*ell,rel_tol=1e-11)

x=math.exp(-1);z=1+x+x*x
assert (2*x+x*x)/z-(x+2*x*x)/z>0
rows=[]
for L in [100,1000,10000]:
    V=L**3;p=2*math.pi/L;e,a,v2=coeff(p);m=math.floor(V/a)
    D=e*m-math.log(-math.expm1(-e))
    diff=a*(m-1/math.expm1(e))/V
    rows.append(dict(L=L,relative_entropy_density=D/V,occupation_difference_density=diff))
assert rows[-1]['relative_entropy_density']<1e-6
assert rows[-1]['occupation_difference_density']>.99
assert rows[-1]['relative_entropy_density']<rows[0]['relative_entropy_density']/1000
# Negative controls: these are deliberately false in the explicitly computed models.
neg={
 'same_spectrum_forces_same_occupation':math.isclose((2*x+x*x)/z,(x+2*x*x)/z),
 'vanishing_entropy_density_forces_vanishing_occupation_density':rows[-1]['occupation_difference_density']<.01,
 'fixed_positive_tilt_stable_at_all_small_momenta':all((p*p+1-.01)**2-1>0 for p in [.1,.01,.001]),
}
assert not any(neg.values())
print(json.dumps({'nonproof':True,'rows':rows,'false_claims_rejected':list(neg)},indent=2))
