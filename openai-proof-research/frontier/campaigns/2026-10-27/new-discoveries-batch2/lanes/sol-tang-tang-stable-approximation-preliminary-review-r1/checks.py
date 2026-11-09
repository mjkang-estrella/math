"""Diagnostics only; analytic transport proof is in review.md. Run through helper_guard."""
import json, math
from pathlib import Path
import mpmath as m
m.mp.dps = 35
a=m.mpf(2)/3
theta=m.pi*a
def p(u):
    if u==0:return m.mpf(1)
    if u==1:return m.mpf(0)
    r=(m.sin(theta*u)/m.sin(theta*(1-u)))**(1/a)
    return 1/(1+r)
rows=[]
for t in [-6,-2,0,2,6]:
    z=m.exp(t)
    integ=m.quad(lambda u: z*p(u)/(1-p(u)+z*p(u)),[0,m.mpf('.5'),1])
    error=abs(integ-z**a/(1+z**a))
    assert error < m.mpf('1e-27')
    rows.append({'tilt':t,'Stieltjes_error':str(error)})
mid=[]
for n in [8,32,128]:
    ps=[p(m.mpf(2*j-1)/(4*n)) for j in range(1,2*n+1)]
    assert len(ps)==2*n and all(0<x<1 for x in ps)
    assert abs(sum(ps)-n)<m.mpf('1e-29')
    errs=[]
    for t in [-4,-1,1,4]:
        f=sum(m.log(1+x*m.expm1(t)) for x in ps)/n
        exact=3*m.log((1+m.exp(a*t))/2)
        errs.append(str(abs(f-exact)))
    mid.append({'n':n,'log_mgf_errors':errs,'endpoint_log_mass_per_n':str(sum(m.log(1-x) for x in ps)/n),'target_endpoint_rate':str(-3*m.log(2))})
out={'purpose':'independent bounded quadrature and midpoint diagnostics; no finite transport/O(1) claim','Stieltjes':rows,'midpoints':mid}
Path(__file__).with_name('check-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
