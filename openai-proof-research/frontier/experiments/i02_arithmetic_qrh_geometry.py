# Re-derivation of the 7/8 boundary from the pinned manuscript's geometry, and
# the room left by its endpoint certificate if the prime-slot length ell is varied.
# Formulas transcribed from QuasiRH Sept-30 paper.tex: old-eq:5.1, old-eq:5.10/5.11,
# eq:stage-high-exponent, prop:detector-counts, lem:balanced-endpoint.
from fractions import Fraction as Fr
import itertools
def geom(ell,b):
    h=(1+3*ell+b)/2; lx=1+ell-h; ly=lx+b
    sigma0=1-h/6+b/12          # C(sigma0)= lx/2+b/12 with C(s)=lx/2+s-1+h/6
    return h,lx,ly,sigma0
h,lx,ly,s0=geom(Fr(1,6),Fr(1,8))
print("paper geometry h,lx,ly,sigma0:",h,lx,ly,s0)
assert (h,lx,ly,s0)==(Fr(13,16),Fr(17,48),Fr(23,48),Fr(7,8))
# symbolic identity sigma0 = 11/12 - ell/4 (independent of b)
for ell,b in itertools.product([Fr(k,60) for k in range(0,13)],[Fr(k,64) for k in range(0,17)]):
    assert geom(ell,b)[3]==Fr(11,12)-ell/4
print("identity sigma0 = 11/12 - ell/4 verified on grid")
alpha=5/6
def Eh(ell,b,delta,x):
    h=(1+3*ell+b)/2
    Px=(2-8*x/9)*(1-x); Dx=3-17*x/9
    J=(alpha-delta)*Dx+delta*Px
    R=1-delta+(alpha-delta)*delta*Px/(2*J)
    q=x*delta
    return -0.75-ell/4-b/3+h*R+delta*(1+2*ell)/2+q*ell
def worst(ell,b,n=400):
    m=-1e9
    for i in range(n+1):
        d=1/50+(alpha-1/50)*i/n
        for j in range(41):
            m=max(m,Eh(ell,b,d,0.5*j/40))
    return m
w=worst(1/6,1/8); print("paper worst E(h) =",w," certificate bound -49/440640 =",-49/440640)
# floor constraint: -1/4+5ell/4+b/6+delta0(1+3ell)/2<0
lo,hi=1/6,0.2
for _ in range(60):
    mid=(lo+hi)/2
    ok=worst(mid,1/8)<0 and (-0.25+5*mid/4+(1/8)/6+(1/50)*(1+3*mid)/2)<0
    lo,hi=(mid,hi) if ok else (lo,mid)
print("max ell with b=1/8 (row counts fixed):",lo," sigma0 =",11/12-lo/4," gain =",7/8-(11/12-lo/4))
best=None
for bb in [k/400 for k in range(0,81)]:
    lo,hi=0.0,0.25
    for _ in range(50):
        mid=(lo+hi)/2
        ok=worst(mid,bb,120)<0 and (-0.25+5*mid/4+bb/6+(1/50)*(1+3*mid)/2)<0
        lo,hi=(mid,hi) if ok else (lo,mid)
    if best is None or lo>best[0]: best=(lo,bb)
print("best over b (coarse):",best," sigma0=",11/12-best[0]/4)
# density-hypothesis-quality counts R=1-delta, q=delta/2, floor delta0->0: ell<1/5-2b/15
print("architecture ceiling with ideal counts, b->0: sigma0 >=",11/12-0.2/4,"=13/15",13/15)
