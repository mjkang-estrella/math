"""Reconstruct the exponential identity as a Laurent polynomial in X,Y.
X=exp(t), Y=exp(sqrt(17)t). Uses exact rational arithmetic only.
"""
from check import F,Z,O,add,neg,sub,scale,mul,power,sign,enc,p,U,V,freq
from math import isqrt
import json
def plus(A,B):
    C=A.copy()
    for k,v in B.items():C[k]=add(C.get(k,Z),v)
    return {k:v for k,v in C.items() if v!=Z}
def scalar(A,c):return {k:mul(v,c) for k,v in A.items() if mul(v,c)!=Z}
def times(A,B):
    C={}
    for (i,j),v in A.items():
        for (k,l),w in B.items():
            key=(i+k,j+l);C[key]=add(C.get(key,Z),mul(v,w))
    return {k:v for k,v in C.items() if v!=Z}
def deriv(A):return {k:mul(v,(F(k[0]),F(k[1]))) for k,v in A.items() if k!=(0,0)}
def cosh(i,j):return {(i,j):(F(1,2),F(0)),(-i,-j):(F(1,2),F(0))}
def sinh(i,j):return {(i,j):(F(1,2),F(0)),(-i,-j):(F(-1,2),F(0))}
def rational(A,c):return scalar(A,(F(c),F(0)))
A=rational(plus(plus(cosh(4,0),rational(times(cosh(1,0),cosh(0,1)),-1)),scalar(times(sinh(1,0),sinh(0,1)),(F(0),F(5,17)))),F(1,2))
B=rational(times(sinh(1,0),plus(cosh(5,0),rational(cosh(0,1),-1))),F(1,2))
u=plus(plus(times(deriv(B),A),rational(times(B,deriv(A)),-1)),rational(times(A,A),-1))
v=rational(times(B,A),-4)
assert u==U and v==V
def moment(poly,n):
    val=Z
    for lam,c in poly.items():val=add(val,mul(c,power(lam,n)))
    return val
small=[]
for n in range(24):
    E=moment(u,n)
    if n:E=add(E,scale(moment(v,n-1),n))
    if n>=2:E=add(E,scale(moment(u,n-2),2*n*(n-1)))
    assert E[1]==0
    assert sign(E)==(1 if n>=10 and n%2==0 else 0)
    small.append({'n':n,'derivative':str(E[0])})
cert=json.loads((p/'checks.json').read_text())['success']
assert cert['N']==24
prefix=[tuple(map(F,c)) for row in cert['rows'] for c in row['prefix']]
interval=None
for k in range(1,20):
    den=10**k; num=isqrt(17*den*den)
    lo,hi=F(num,den),F(num+1,den)
    assert lo*lo<17<hi*hi
    bounds=[a+b*(lo if b>=0 else hi) for a,b in prefix]
    if min(bounds)>0:
        interval={'decimal_digits':k,'lower':str(lo),'upper':str(hi),'prefix_lower_bounds':list(map(str,bounds))};break
assert interval
assert all(sign(sub(freq[i],freq[i+1]))>0 for i in range(len(freq)-1))
# Independently differentiate the polynomial-exponential expression 24 times.
Epoly={}
for lam,c in u.items():
    Epoly[(0,lam)]=c;Epoly[(2,lam)]=scale(c,2)
for lam,c in v.items():Epoly[(1,lam)]=c
for _ in range(24):
    new={}
    for (r,lam),c in Epoly.items():
        if r:new[(r-1,lam)]=add(new.get((r-1,lam),Z),scale(c,r))
        new[(r,lam)]=add(new.get((r,lam),Z),mul(c,lam))
    Epoly={k:c for k,c in new.items() if c!=Z}
pred={}
for lam in u.keys()|v.keys():
    c,d=u.get(lam,Z),v.get(lam,Z)
    pred[(0,lam)]=add(add(mul(c,power(lam,24)),scale(mul(d,power(lam,23)),24)),scale(mul(c,power(lam,22)),1104))
    pred[(1,lam)]=add(mul(d,power(lam,24)),scale(mul(c,power(lam,23)),96))
    pred[(2,lam)]=scale(mul(c,power(lam,24)),2)
pred={k:c for k,c in pred.items() if c!=Z}
assert Epoly==pred
result={'status':'PASS','laurent_identity_terms':{'A':len(A),'B':len(B),'U':len(u),'V':len(v)},'small_derivatives':small,'rational_sqrt17_interval':interval,'exact_prefix_count':len(prefix),'derivative24_identity':True,'scope':'Proves finite identities and certificate inequalities; Abel summation, derivative positivity and analytic assembly supplied in FINDINGS.md. No Lean result.'}
(p/'verification.json').write_text(json.dumps(result,indent=2))
print(json.dumps({'status':'PASS','prefix_count':len(prefix),'rational_interval_digits':interval['decimal_digits']}))
