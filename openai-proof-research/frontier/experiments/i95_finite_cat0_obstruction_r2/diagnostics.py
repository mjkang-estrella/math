"""Finite actual CAT(0) fixtures and exact parameter checks; not analytic proof."""
import sys
sys.dont_write_bytecode=True
from fractions import Fraction as F
from itertools import product,permutations
from math import isqrt
import json

def norm2(x):return sum(t*t for t in x)
def d2(x,y):return norm2(tuple(a-b for a,b in zip(x,y)))
def lerp(x,y,t):return tuple((1-t)*a+t*b for a,b in zip(x,y))
def td(x,y):return abs(x[1]-y[1]) if x[0]==y[0] else x[1]+y[1]
def tl(x,y,t):
    if x[0]==y[0]:return (x[0],(1-t)*x[1]+t*y[1])
    l=t*td(x,y)
    return (x[0],x[1]-l) if l<=x[1] else (y[0],l-x[1])
def sqrtup(x):
    den=2**100;k=isqrt(x.numerator*den*den//x.denominator)
    if F(k*k,den*den)<x:k+=1
    assert F(k*k,den*den)>=x
    return F(k,den)

def run():
    counts={}
    # Perturbed actual Euclidean triangles in R^3, using rational coordinates.
    w=(F(0),)*3;basep=(F(1),)*3;basez=(F(1),F(1),F(0));n=0
    for den in [2**k for k in range(9,17)]:
        for dp in product([-1,0,1],repeat=3):
            p=tuple(v+F(a,den) for v,a in zip(basep,dp))
            for dz in [(-1,0,1),(0,1,-1),(1,-1,0),(0,0,0)]:
                z=tuple(v+F(a,den) for v,a in zip(basez,dz));c=lerp(p,w,F(1,2));j=lerp(z,w,F(1,2))
                eps=max(abs(d2(p,w)-3),abs(d2(z,w)-2),abs(d2(p,z)-1),abs(d2(z,c)-F(3,4)))
                assert eps<=F(1,16)
                assert (d2(c,j)-F(1,4))**2<=4*eps
                for q in [F(2,5),F(1,2),F(1),F(2),F(5,2)]:
                    lhs=d2(p,j)+d2(z,c)-d2(p,c)-d2(z,j)
                    assert abs(lhs)<=q*d2(p,z)+d2(c,j)/q
                n+=1
    counts['actual_R3_reverse_median']=n
    pts=[(b,F(k,4)) for b in range(3) for k in range(1,4)]+[(0,F(0))]
    n=0
    for p,z,c,j in permutations(pts,4):
        lhs=td(p,j)**2+td(z,c)**2-td(p,c)**2-td(z,j)**2
        for q in [F(2,5),F(1,2),F(1),F(2),F(5,2)]:
            assert abs(lhs)<=q*td(p,z)**2+td(c,j)**2/q;n+=2
    counts['tripod_Young_both_orientations']=n
    n=0
    for y,H,K in product(pts,repeat=3):
        def deficit(t):return (1-t)*td(K,y)**2+t*td(K,H)**2-t*(1-t)*td(y,H)**2-td(K,tl(y,H,t))**2
        vals=[deficit(F(k,12)) for k in range(13)]
        assert vals[0]==vals[-1]==0 and all(0<=v<=2*vals[6] for v in vals)
        assert all(2*vals[k]>=vals[k-1]+vals[k+1] for k in range(1,12));n+=1
    counts['tripod_interpolation_deficits']=n
    n=0
    for a,b in product(pts,repeat=2):
        mid=tl(a,b,F(1,2))
        for approx in [tl(mid,(0,F(0)),F(1,7)),tl(mid,pts[-2],F(1,13))]:
            rho=td(mid,approx)
            for endpoint in [a,b]:
                assert (4*td(approx,endpoint)**2-td(a,b)**2)**2<=(16*rho)**2;n+=1
            for z in pts+[mid,approx,a,b]:
                row=4*td(approx,z)**2-2*td(a,z)**2-2*td(b,z)**2+td(a,b)**2
                assert row<=16*rho;n+=1
    counts['tripod_approx_midpoint_endpoints_all_z']=n
    n=0
    for k in range(1,25):
        eps=F(1,2**k);o=(0,eps);p=(1,1-eps);q=(2,1-eps)
        assert td(o,p)==td(o,q)==1 and td(p,q)==2-2*eps
        for t in [eps/2,eps,F(1,3),F(2,3),F(1)]:
            assert td(tl(o,p,t),tl(o,q,t))==2*max(t-eps,0);n+=1
        assert tl(o,p,eps/2)==tl(o,q,eps/2)
    counts['rooted_tree_fixed_fractions']=n
    n=0
    for lam,o in product([F(1,2**k) for k in range(1,17)],[F(-2),F(0),F(3)]):
        p=lam*o/(4+lam)
        assert 4*p*p+lam*(o-p)**2<=4*o*o
        assert 2*abs(p)==lam*abs(o-p)/2
        if o:assert 4*p*p<=4*o*o/4
        n+=1
    counts['reflection_proximal_exact']=n
    n=0
    for t in range(1,11):
        leaves=list(product([-1,1],repeat=t));mean=[F(sum(v),t) for v in leaves]
        # h is maximally dependent on the leaves; its norm bound alone suffices.
        adaptive=sum(abs(v) for v in mean)/len(mean)
        assert adaptive**2<=F(1,t)
        assert sum(v*v for v in mean)/len(mean)==F(1,t);n+=len(leaves)
    counts['adaptive_common_I_leaf_lists']=n
    n=0
    for den in [2**k for k in range(1,25)]:
        eta=F(1,den)
        # Signed bounded observable; TV convention is half the l1 difference.
        for x,y in product(range(-12,13),repeat=2):
            assert abs(eta*(x-y))<=24*eta;n+=1
    counts['signed_TV_cases']=n
    # Exact constants without materializing or stringifying giant parameter integers.
    assert 16*12**2*4==9216
    assert 16*12**2*6*4==55296
    assert 32*12**2*6**2*4==663552
    assert F(72,663552)==F(1,9216)
    assert F(2000,10000)<1 and 80032==8*10004
    assert F(275,9)<36
    assert F(17,4)+63<68 and 17+68+63==148
    assert F(148,65536)<F(1,16) and F(21,65536)<F(1,4)
    assert F(3,4)+F(68,65536)<1
    assert 4*148<25**2 and 25+5*(21+2)==140
    assert F(8*68+7+2*8+2*16,9)<67
    assert 68+1<81 and 67<81 and 140+27==167
    assert 6*167+5*68+16+8*18+16<=1523
    assert F(140)+F(1523,4)<529
    assert 32*23<2000 and 1523<=2000
    # e^(1/4)<=e^(1/8) at e<=1; no addition of max initial/row errors is needed.
    n=0
    for k in [4,5,6,8,12,16]:
        u=F(1,2**k);e=u**8;h=21*u**4;s=sqrtup(2*e)
        R=17*e/4+3*h;E0=17*e+R+3*h;F0=2*sqrtup(E0)+5*(h+s)
        U=3*e/2+3*s;L=U+8*e;V=8*R/9+7*e/9+2*U/9+2*L/9
        r0=sqrtup(R+e);f=F0+3*r0;w0=sqrtup(V)+r0;Om=6*f+5*R+16*e+8*w0+L
        assert E0<=F(1,16) and F0<=140*u*u and Om<=1523*u*u
        assert sqrtup(F0+Om/4)<=23*u
        n+=1
    counts['outward_sqrt_envelope_cases']=n
    # §7 normalized by T; all integer-power targets have nonnegative integer exponents.
    assert F(8+90,392)==F(1,4)
    assert min(F(8-7,392),F(1,392*5),F(1,392))==F(1,1960)
    assert 4*15*18*1960==2116800 and 60*1960==117600
    for T in [1,2,3,17,100]:
        for m in [1,2,3]:
            base=2*m;exp=392*T;N=base**exp
            assert N%2==0
            target=base**(exp-1)
            assert target*base==N and F(exp-1,exp)==1-F(1,392*T)
    counts['integer_subsequence_fixtures']=15
    return {'status':'PASS_FINITE_DIAGNOSTICS_ONLY','checks':counts}
if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
