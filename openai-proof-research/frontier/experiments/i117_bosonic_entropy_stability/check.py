"""Finite exact diagnostics, not proofs of the infinite-dimensional claims.

Logarithms are enclosed by rational atanh series after range reduction.
For 1 <= x <= 2, z=(x-1)/(x+1) lies in [0,1/3]; truncation after J
terms has remainder between 0 and
2*z**(2*J+1)/((2*J+1)*(1-z*z)). Negative coefficients reverse bounds.
No floating point root or spectral assertion is used.
"""
from fractions import Fraction as F
from functools import lru_cache

def add(a,b): return (a[0]+b[0],a[1]+b[1])
def scale(c,a): return (c*a[0],c*a[1]) if c>=0 else (c*a[1],c*a[0])

def series(x,J=36):
    z=(x-1)/(x+1)
    s=sum((2*z**(2*j+1)/F(2*j+1) for j in range(J)),F(0))
    return s,s+2*z**(2*J+1)/((2*J+1)*(1-z*z))

@lru_cache(None)
def log_bounds(x):
    x=F(x)
    assert x>0
    e=0
    while x<1: x*=2; e-=1
    while x>2: x/=2; e+=1
    return add(series(x),scale(e,series(F(2))))

def xlog(x): return (F(0),F(0)) if not x else scale(x,log_bounds(x))
def entropy_binary(p): return scale(-1,add(xlog(p),xlog(1-p)))
def g(x): return add(xlog(x+1),scale(-1,xlog(x)))

def entropy_tail(n,x,p,k):
    a=(1-p)/(x+1)**n*(x/(x+1))**k
    ambiguity=add(xlog(a+p),scale(-1,add(xlog(a),xlog(p))))
    return add(add(scale((1-p)*n,g(x)),entropy_binary(p)),scale(-1,ambiguity))

def run():
    counts={}
    count=0
    for r in [F(1,4),F(1),F(3),F(7)]:
        for b in [F(1,8),F(1,2),F(2),F(9)]:
            for eta in [F(1,10),F(1,3),F(1,2),F(9,10)]:
                s=eta*r+(1-eta)*b
                u=(eta+min(F(1),s/r))/2
                t=eta/u
                c=(s-u*r)/(1-u)
                assert eta<u<1 and 0<t<1 and c>0
                assert u*t==eta
                assert u*(1-t)*r+(1-u)*c==(1-eta)*b
                assert u*(1-t)*(r+F(1,2))+(1-u)*(c+F(1,2))==(1-eta)*(b+F(1,2))
                count+=1
    counts['exact_channel_factorizations']=count
    count=0
    for k in [32,64,128,256]:
        p=F(1,2*k)
        target=scale(2,g(F(1)))
        low=entropy_tail(2,F(1,2),p,k)
        high=entropy_tail(2,F(1),p,k)
        assert low[1]<target[0]<target[1]<high[0]
        # Uniform edge lower bound for x in [1/2,1], r=1, c=1/2.
        assert F(1,k)>=F(1,2**(k-1))
        assert 2**((k-2)//2)>=k
        count+=1
    counts['rational_entropy_root_brackets']=count
    count=0
    for n in range(2,6):
        r=F(1)
        p0=F(1,2**n)
        c=F(1,2)
        for k in [64,128,256,512]:
            pk=p0/F(2**k)
            d=p0-pk
            z=c/(k*d)  # sin(theta)^2; all squared matrix entries rational
            assert 0<z<1
            diagonal_low=p0-d*z
            diagonal_high=pk+d*z
            off_squared=d*d*z*(1-z)
            assert diagonal_low*diagonal_high-off_squared==p0*pk
            assert diagonal_low+diagonal_high==p0+pk
            assert k*(diagonal_high-pk)==c
            assert d*d*z==c*d/k
            assert (r+1)**2*k*off_squared==(r+1)**2*(c*d-c*c/k)
            assert n*r+c<n*r+1
            count+=1
    counts['entropy_preserving_rotation_identities']=count
    # The cited external scalar inequality is literally false.
    assert abs(F(1)-F(-1))**2 > (F(1)**2+F(-1)**2)/2
    counts['external_literal_countercheck']=1
    return {'status':'PASS','counts':counts,
            'scope':'Exact finite rational/channel/entropy-bracket diagnostics; no universal-proof or substantiality certification'}

if __name__=='__main__':
    import json
    print(json.dumps(run(),indent=2,sort_keys=True))
