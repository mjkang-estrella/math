"""Explore Davis Conjecture 3.1 using a positive-weight variance identity.

This is a high-precision search, not a proof or a certified numerical bound.
"""
from pathlib import Path
import json
import mpmath as mp
mp.mp.dps=75

def value(d,x):
    # The common scale of these nonnegative weights cancels.
    f=[mp.mpf(1)]
    facts=[1]
    for i in range(1,d+1):
        f.append(f[-1]*(x-i+1))
        facts.append(facts[-1]*i)
    w=[f[i]**2*f[d-i]**2/(facts[i]*facts[d-i]) for i in range(d+1)]
    z=mp.fsum(w)
    var=mp.fsum(w[i]*(mp.mpf(i)-mp.mpf(d)/2)**2 for i in range(d+1))/z
    neg_R_over_P=(d-4*var)/(2*(d+1))
    return 1-neg_R_over_P*(2*x+d-2)/(d-2)

ds=list(range(5,101))+list(range(125,1001,25))
scales=[mp.mpf(v) for v in ['1','1.001','1.01','1.05','1.2','1.5','2','3','5','10','100']]
rows=[]
worst=(mp.ninf,None,None)
for d in ds:
    b=(d+mp.sqrt(d+2))/2
    for s in scales:
        x=b*s
        q=value(d,x)
        rows.append(dict(d=d,x=str(x),Q=str(q),boundary_multiple=str(s)))
        if q>worst[0]: worst=(q,d,x)
report=dict(method="75-digit positive-weight variance evaluation",cases=len(rows),
            counterexamples=[r for r in rows if mp.mpf(r['Q'])>mp.mpf('.005')],
            worst=dict(Q=str(worst[0]),d=worst[1],x=str(worst[2])),
            discovery_credit=0,rows=rows)
Path(__file__).with_name('davis-search.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k!='rows'}))
