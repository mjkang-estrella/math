"""Independent Fraction checks of the proof's finite-sum identities."""
from fractions import Fraction as Q
from math import factorial
from pathlib import Path
import json

def weights(d,x):
    f=[Q(1)]
    for i in range(d): f.append(f[-1]*(x-i))
    return [f[i]**2*f[d-i]**2/Q(factorial(i)*factorial(d-i)) for i in range(d+1)]

cases=0
zero_weight_cases=0
for d in range(2,31):
    D=Q(d,2)
    for a in [Q(1),Q(3,2),Q(2),Q(7,3),Q(10),Q(100)]:
        x=D+a;w=weights(d,x);z=sum(w);wn=weights(d+1,x)
        assert z>0
        V=sum(v*(i-D)**2 for i,v in enumerate(w))/z
        M=sum(v*(i-D)**4 for i,v in enumerate(w))/z
        assert sum(v*i for i,v in enumerate(w))/z==D
        assert sum(wn)/z==2*sum(v*(x-i)**2 for i,v in enumerate(w))/((d+1)*z)
        q=2*x*x/(d+1)-2*d*x/(d+1)+D
        assert q-sum(wn)/z==(d-4*V)/(2*(d+1))
        for i in range(d):
            assert (d-i)*(x-i)**2*w[i] == (i+1)*(x-d+i+1)**2*w[i+1]
        B=4*D*a-D+2*a*a-2*a
        assert 2*M+B*V==D*a*a
        assert M>=V*V
        cases+=1
        zero_weight_cases+=any(v==0 for v in w)
report=dict(method='Fraction evaluation of literal falling products and moments',cases=cases,
            cases_with_zero_weights=zero_weight_cases,failures=0,discovery_credit=0)
Path(__file__).with_name('moment-check.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
