#!/usr/bin/env python3
"""Independent exact finite checks. No approximation of the actual infinite L."""
from fractions import Fraction as F
from math import comb
from pathlib import Path
import json

def alpha(j,x):
    k=j if j>=0 else -1-j
    if not k: return 10
    lower,base=1,2
    while k>=8*lower: lower*=8; base*=2
    t=x%base
    return 10*(k+1)+100*(base-2)+100*(t if j>=0 else base-1-t)

# Independent closed drift sums from eq:b-positive and eq:b-negative.
log_checks=0
L_bounds=[]
N=4102
for x in range(-16,16):
    ax={j:alpha(j,x) for j in range(-N-1,N+1)}
    ay={j:alpha(j,x+1) for j in range(-N-1,N+1)}
    w={0:0}; v={0:0}; bp={0:0}
    for n in range(1,N+1):
        w[n]=w[n-1]-ax[n-1]; v[n]=v[n-1]-ay[n-1]
        w[-n]=w[1-n]+ax[-n]; v[-n]=v[1-n]+ay[-n]
    pos=neg=0
    for n in range(1,N):
        pos+=ay[n-1]-ax[n-1]
        neg+=ay[-n]-ax[-n]
        bp[n]=-pos+ay[n-1]-10
        bp[-n]=neg+ay[-n-1]-10
    for j in range(-4100,4101):
        assert bp[j]+w[j]-v[j-1]==-10
        assert bp[j+1]-bp[j]==ax[j]-ay[j-1]
        log_checks+=1
for m in range(1,5):
    x=2**m-1; n=8**m
    actual=-sum(alpha(k,x+1)-alpha(k,x) for k in range(n))+alpha(n-1,x+1)-10
    lower=100*(2**m-1)*7*8**(m-1)
    assert actual>=lower
    L_bounds.append({'m':m,'log_b_at_residue':actual,'lower_bound':lower})

I=((F(1),F(0)),(F(0),F(1)))
O=((F(0),F(0)),(F(0),F(0)))
z=(F(0),F(0))
def mul(a,b): return tuple(tuple(sum(a[i][k]*b[k][j] for k in range(2)) for j in range(2)) for i in range(2))
def inv(a):
    d=a[0][0]*a[1][1]-a[0][1]*a[1][0]
    return ((a[1][1]/d,-a[0][1]/d),(-a[1][0]/d,a[0][0]/d))
def vec(a,v): return tuple(sum(a[i][k]*v[k] for k in range(2)) for i in range(2))
def plus(a,b): return tuple(x+y for x,y in zip(a,b))
def scale(c,v): return tuple(c*x for x in v)
def power(a,n):
    r=I
    for _ in range(n): r=mul(r,a)
    return r
Ws=[I,((F(1),F(1)),(F(0),F(1))),((F(2),F(0)),(F(1),F(1))),((F(1),F(2)),(F(1),F(3))),((F(3),F(1)),(F(2),F(1)))]
def W(j): return Ws[j%len(Ws)]
def A(j): return mul(W(j+1),inv(W(j)))
Cs=[((F(1,3),F(2,5)),(F(0),F(1,2))),((F(0),F(1)),(F(0),F(0))),O,((F(1),F(2)),(F(0),F(0))),((F(1),F(-1)),(F(2),F(0)))]
commutation=reflection=boundary=orbits=extraction=0
for C in Cs:
    def D(j): return mul(mul(W(j-1),C),inv(W(j)))
    def apply(f):
        if not f: return {}
        return {j:plus(vec(A(j-1),f.get(j-1,z)),vec(D(j+1),f.get(j+1,z))) for j in range(min(f)-1,max(f)+2)}
    for j in range(-31,32):
        assert mul(A(j-1),D(j))==mul(D(j+1),A(j))
        assert mul(mul(inv(W(j-1)),D(j)),W(j))==C
        commutation+=1
    for sign in (1,-1):
        for n in range(1,12):
            h={0:(F(2),F(-3)) if sign==1 else z}
            for j in range(1,n+1):
                h[j]=(F(j*j+1,3),F(2-j,7)); h[-j]=scale(sign,vec(power(C,j),h[j]))
            f={j:vec(W(j),v) for j,v in h.items()}
            k={j:vec(inv(W(j)),v) for j,v in apply(f).items()}
            for j in range(1,n+2):
                assert k[-j]==scale(sign,vec(power(C,j),k[j])); reflection+=1
            if sign==-1: assert k[0]==z
            boundary+=1
    # Compute orbit in original coordinates, then peel off smaller pairs.
    g=(F(3,7),F(-5,11)); f={0:g}
    for n in range(13):
        expected={n-2*l:vec(W(n-2*l),scale(comb(n,l),vec(power(C,l),g))) for l in range(n+1)}
        assert all(f.get(j,z)==expected.get(j,z) for j in set(f)|set(expected)); orbits+=1
        peeled=dict(f)
        for l in range(1,n//2+1):
            j=n-2*l; v=scale(comb(n,l),vec(power(C,l),g))
            peeled[j]=plus(peeled.get(j,z),scale(-1,vec(W(j),v)))
            if j: peeled[-j]=plus(peeled.get(-j,z),scale(-1,vec(W(-j),vec(power(C,j),v))))
        target={0:g} if n==0 else {n:vec(W(n),g),-n:vec(W(-n),vec(power(C,n),g))}
        assert all(peeled.get(j,z)==target.get(j,z) for j in set(peeled)|set(target)); extraction+=1
        f=apply(f)
# Noncommutativity really exercised, not just claimed.
assert mul(A(1),A(2))!=mul(A(2),A(1))
assert mul(W(1),Cs[0])!=mul(Cs[0],W(1))
# A concrete asymmetric coupling d_j=1 (j<=0), 2 (j>=1) defeats both old graphs.
C=Cs[0]; g=(F(1),F(0)); c2=vec(power(C,2),g)
assert c2!=z
for sign in (1,-1):
    h={2:g,-2:scale(sign,c2)}
    k=lambda j: plus(h.get(j-1,z),scale(1 if j<=0 else 2,vec(C,h.get(j+1,z))))
    assert k(-1)!=scale(sign,vec(C,k(1)))
# Output multiplication cannot be silently moved through base translation.
a=[F(1)+F(i,8) for i in range(8)]
assert any(a[x]!=a[(x-1)%8] for x in range(8))
result={'status':'pass','independent_integer_log_checks':log_checks,'residues':[-16,15],'indices':[-4100,4100], 'normalizer_lower_bound_checks':L_bounds,'bounded_periodic_noncommuting_models':len(Cs),'block_checks':commutation,'reflection_relations':reflection,'boundary_cases':boundary,'original_coordinate_orbits':orbits,'triangular_extractions':extraction,'asymmetric_coupling_rejects_both_old_graphs':True,'normalizer_L_approximated':False,'scope':'Exact finite algebra only; infinite-dimensional claims are proved in the review.'}
Path(__file__).with_name('independent_output.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
