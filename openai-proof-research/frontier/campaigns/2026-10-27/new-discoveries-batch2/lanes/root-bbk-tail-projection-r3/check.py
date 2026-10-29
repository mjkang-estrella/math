import os
for name in ('OPENBLAS_NUM_THREADS', 'OMP_NUM_THREADS', 'MKL_NUM_THREADS'):
    os.environ[name] = '1'
import resource
resource.setrlimit(resource.RLIMIT_AS, (512*1024**2, 512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU, (90, 90))
import sympy as s
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path
import json, sys, math

x = s.Symbol('x')
R = s.Poly(x**105 - 1, x, domain=s.QQ)
one = s.Poly(1, x, domain=s.QQ)

@lru_cache(None)
def phi(d):
    return s.Poly(s.cyclotomic_poly(d, x), x, domain=s.QQ)

def projection(k,n):
    numer = list(range(2*k-1, 2*k+2*n-1, 2))
    denom = list(range(1, 2*n+2, 2))
    exponents = {}
    for sign, terms in ((1,numer),(-1,denom)):
        for h in terms:
            for d in s.divisors(h):
                exponents[d] = exponents.get(d,0) + sign
    assert all(e >= -1 for e in exponents.values())
    A = one
    B = one
    N = one
    for d,e in exponents.items():
        if e == -1:
            if 105 % d == 0: A *= phi(d)
            else: B = (B*phi(d)).rem(R)
        elif e > 0:
            for _ in range(e): N = (N*phi(d)).rem(R)
    C = R.exquo(A)
    inv = s.invert(B,R)
    P = (N*C*inv).rem(R)
    assert (P*B-N*C).rem(R).is_zero
    values = [P.nth(i) for i in range(105)]
    mean = s.Rational(math.prod(numer),math.prod(denom))
    assert sum(values) == 105*mean
    return values,mean

# Each cube dual has -1 on one opposite pair and +1 on the other six.
# Its sums on fibres of any proper divisor of 105 are nonnegative.
residue = {(r%3,r%5,r%7):r for r in range(105)}
duals=[]
for pairs in product(*(list(combinations(range(p),2)) for p in (3,5,7))):
    vertices=[residue[tuple(pairs[j][b[j]] for j in range(3))]
              for b in product((0,1),repeat=3)]
    for i in range(4):
        signs=[-1 if j in (i,7-i) else 1 for j in range(8)]
        for d in (1,3,5,7,15,21,35):
            assert all(sum(y for r,y in zip(vertices,signs) if r%d==a)>=0
                       for a in {r%d for r in vertices})
        duals.append((vertices,signs))

def analyze(k,n):
    assert 2*n+1 < 105
    v,mean=projection(k,n)
    margin,idx=min((sum(y*v[r] for r,y in zip(rs,ys)),i)
                   for i,(rs,ys) in enumerate(duals))
    out={'k':k,'n':n,'mean':str(mean),'minimum_projected_coefficient':str(min(v)),
         'minimum_cube_dual':str(margin),'dual_normalized_by_mean':str(margin/mean),
         'minimizing_dual':duals[idx], 'projection':[str(a) for a in v]}
    return out

if __name__=='__main__':
    cases=[tuple(map(int,t.split(','))) for t in sys.argv[1:]] or [(20,17),(30,25),(60,51)]
    results=[]
    for k,n in cases:
        r=analyze(k,n);results.append(r)
        print(json.dumps({a:b for a,b in r.items() if a!='projection'}),flush=True)
        Path(__file__).with_name('checks.json').write_text(json.dumps({'period':105,'duals':len(duals),'cases':results,
            'scope':'Exact necessary-condition diagnostics only; no conjecture proof or novelty clearance.'},indent=2)+'\n')
