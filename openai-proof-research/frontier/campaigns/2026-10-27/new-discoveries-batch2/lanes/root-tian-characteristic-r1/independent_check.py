from check import data, fmt
import sympy as s
import json
from pathlib import Path

t=((None,(None,None)),((None,None),None))
z=s.symbols('z0:6'); x=s.Symbol('x'); it=iter(z)
def build(t):
    if t is None: return next(it)
    return build(t[0])**2+build(t[1])**3
P=s.expand(build(t)); diagonal={v:x for v in z}
def depths(t,l=0,r=0):
    return [(l,r)] if t is None else depths(t[0],l+1,r)+depths(t[1],l,r+1)
def val(n,p):
    n=abs(int(n)); v=0
    while n%p==0: n//=p;v+=1
    return v
expected=data(t)[1]; rows=[]
for i,(l,r) in enumerate(depths(t)):
    w=s.Poly(s.diff(P,z[i]).subs(diagonal),x)
    coeff=[c for c in w.all_coeffs() if c]
    assert min(val(c,2) for c in coeff)==l
    assert min(val(c,3) for c in coeff)==r
    bits=0
    for (j,),c in w.terms():
        assert int(c)%2**l==0
        if (int(c)//2**l)%2: bits|=1<<j
    assert bits==expected[i][1]
    rows.append({'leaf':i,'L':l,'R':r,'mod2_normalized':hex(bits)})
result={'tree':fmt(t),'literal_multivariate_differentiation':'PASS',
        'exact_contents_and_bitsets':'PASS','rows':rows}
Path(__file__).with_name('independent-check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
