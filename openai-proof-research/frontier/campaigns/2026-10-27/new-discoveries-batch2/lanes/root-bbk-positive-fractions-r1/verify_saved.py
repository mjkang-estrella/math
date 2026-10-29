"""Independent exact verification of saved witnesses; no LP or NumPy import."""
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(45,45))
import json
from fractions import Fraction
from pathlib import Path

def mul(a,b):
    c={}
    for i,x in a.items():
        for j,y in b.items():c[i+j]=c.get(i+j,0)+x*y
    return {i:x for i,x in c.items() if x}

def prod(ds):
    a={0:1}
    for d in ds:a=mul(a,{0:1,d:-1})
    return a

records=json.loads(Path('results.json').read_text())+json.loads(Path('selected-results.json').read_text())
seen=set();fractional=0
for r in records:
    k,n=r['k'],r['n'];assert (k,n) not in seen;seen.add((k,n))
    assert r.get('exact_certificate')
    z=[{} for _ in range(n+1)];D=2*n*(k-2)-1
    for t in r['nonzero']:
        j,a,v=t['j'],t['a'],Fraction(t['coefficient'])
        assert 0<=j<=n and 0<=a<=D+2*j+1 and v>0
        assert a not in z[j]
        z[j][a]=v;fractional+=v.denominator!=1
    lhs={}
    for j in range(n+1):
        term=mul(z[j],prod([2*l+1 for l in range(n+1) if l!=j]))
        for i,v in term.items():lhs[i]=lhs.get(i,0)+v
    lhs={i:v for i,v in lhs.items() if v}
    assert lhs==prod(range(2*k-1,2*k+2*n-1,2)),(k,n)
    # Separate power-series construction, 251 coefficients, used only as a cross-check.
    c=[0]*251;c[0]=1
    for d in range(1,2*n+2,2):
        for i in range(d,251):c[i]+=c[i-d]
    for d in range(2*k-1,2*k+2*n-1,2):
        for i in range(250,d-1,-1):c[i]-=c[i-d]
    for i in range(251):
        assert c[i]==sum(v for j,p in enumerate(z) for a,v in p.items() if i>=a and (i-a)%(2*j+1)==0)
out={'status':'PASS','exact_rational_function_identities':len(seen),'fractional_nonzero_coefficients':fractional,'additional_series_coefficients_checked':251*len(seen),'credit':0,'full_conjecture_proved':False}
Path('independent-verification.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
