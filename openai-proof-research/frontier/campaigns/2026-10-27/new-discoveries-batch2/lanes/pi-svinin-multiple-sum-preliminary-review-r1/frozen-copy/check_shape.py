"""Exact finite screen, NOT a proof of Svinin's unbounded conjectures."""
from fractions import Fraction as Q
from math import comb, factorial
from pathlib import Path
import json
import resource
import time
import sys

resource.setrlimit(resource.RLIMIT_AS, (1024**3, 1024**3))
resource.setrlimit(resource.RLIMIT_CPU, (150, 150))
HERE = Path(__file__).resolve().parent
KMAX = int(sys.argv[1]) if len(sys.argv)>1 else 20
NMAX = (KMAX-1)//3+4

def add(a,b):
    return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
            for i in range(max(len(a),len(b)))]

def linear_mul(a, c):
    """Multiply a(x) by x-c."""
    return add([-c*v for v in a],[Q(0)]+a)

def interpolate(xs, ys):
    d = list(ys)
    out = [Q(0)]
    basis = [Q(1)]
    for j in range(len(xs)):
        out = add(out, [d[0]*v for v in basis])
        d = [(d[i+1]-d[i])/(xs[i+j+1]-xs[i]) for i in range(len(d)-1)]
        basis = linear_mul(basis,xs[j])
    return out

def evaluate(poly,x):
    acc = Q(0)
    for c in reversed(poly): acc = acc*x+c
    return acc

def p_coeffs_at_n(n):
    # Actual source C_{r,q}(n), tracked as multiplicities of tuple SUM.
    dist=[1]
    moments={}
    for r in range(1,KMAX+2):
        nxt=[0]*(len(dist)+n)
        for s,count in enumerate(dist):
            for v in range(1,n+1): nxt[s+v]+=count
        dist=nxt
        assert sum(dist)==n**r
        vals=[0]*(KMAX+1)
        for s,count in enumerate(dist):
            v=s
            for k in range(KMAX+1):
                vals[k]+=count*v
                v*=s*s
        moments[r]=vals
    values={k:[Q(0)] for k in range(1,KMAX+1)}
    t=n*(n+1)
    for j in range(1,KMAX+2):
        weights=[comb(j*(n+1),j-r) for r in range(1,j+1)]
        g=j*comb(j*(n+1)-1,j-1)
        for k in values:
            S=sum(weights[r-1]*moments[r][k] for r in range(1,j+1))
            values[k].append(Q(2**(k+1)*S,t**(k+1)*g))
    out={}
    for k,ys in values.items():
        poly=interpolate([Q(i) for i in range(k+1)],ys[:k+1])
        for j in range(k+1,KMAX+2):
            assert evaluate(poly,Q(j))==ys[j], ('x-polynomial fit failed',n,k,j)
        assert poly[0]==0 and poly[k]==factorial(k)
        for j in range(k):
            out[k,j]=(-1)**j*poly[k-j]
    return out

start=time.monotonic()
table={n:p_coeffs_at_n(n) for n in range(1,NMAX+1)}
alphas=[]
min_alpha=None
for k in range(1,KMAX+1):
    for j in range(k):
        m=j//3
        ns=list(range(1,NMAX+1))
        zs=[Q((n*(n+1))**2,(n*(n+1)+1)**3) for n in ns]
        vals=[table[n][k,j]*Q((n*(n+1))**j,(n*(n+1)+1)**j) for n in ns]
        poly=interpolate(zs[:m+1],vals[:m+1])
        for z,val in zip(zs[m+1:],vals[m+1:]):
            assert evaluate(poly,z)==val, ('shape fit failed',k,j,z)
        for q,alpha in enumerate(poly):
            if alpha<=0:
                raise AssertionError(('nonpositive alpha',k,j,q,alpha))
            min_alpha=alpha if min_alpha is None else min(min_alpha,alpha)
            alphas.append({'k':k,'j':j,'q':q,'alpha':str(alpha)})

# Exact printed anchors (source P2, P3, and P4 constant-in-x coefficient).
lookup={(a['k'],a['j'],a['q']):Q(a['alpha']) for a in alphas}
assert lookup[2,1,0]==Q(2,3)
assert lookup[3,1,0]==Q(16,3)
assert lookup[3,2,0]==Q(4,3)
assert lookup[4,3,0]==Q(24,5)
assert lookup[4,3,1]==Q(8,5)
result={'status':'PASS finite evidence only; no discovery credit',
        'kmax':KMAX,'nmax':NMAX,'j_values_per_n':KMAX+1,
        'shape_alpha_count':len(alphas),'smallest_alpha':str(min_alpha),
        'alphas':alphas,'seconds':time.monotonic()-start,
        'limits':'Polynomial/shape fits checked only at listed integer n,j; not unbounded proofs.'}
(HERE/f'checks-k{KMAX}.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({key:value for key,value in result.items() if key!='alphas'}))
