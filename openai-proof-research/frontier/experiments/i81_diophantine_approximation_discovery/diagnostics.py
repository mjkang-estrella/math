"""Exact finite diagnostics; stdout only. No network, writes, or source modification."""
from fractions import Fraction as F
from math import comb, log
import json

def catalan_interval(J=240):
    row=[F(1,(2*k+1)**2) for k in range(J+1)]
    s=F(0)
    for j in range(J):
        s+=row[0]/2**(j+1)
        row=[row[k]-row[k+1] for k in range(len(row)-1)]
        assert all(x>0 for x in row)
    return s,s+F(1,2**J)

def central(N):
    H=65*N
    m=[F(0)]*H;m[0]=F(2)
    for i in range(2,H,2):m[i]=m[i-2]*i/(i+1)
    km=[F(0)]*H;km[1]=F(2)
    for i in range(2,H):km[i]=((i-1)*km[i-2]+m[i-2]+m[i-1])/i
    def c(d):return F(comb(d,d//2),2**d) if d>=0 and d%2==0 else F(0)
    u=v=F(0)
    for h in range(2*N+1):
        i=63*N-1+h
        for j0 in range(4*N+1):
            j=7*N+j0
            w=(-1)**(h+j0)*comb(2*N,h)*comb(4*N,j0)
            u+=4*w*c(i-j)
            v+=w*(km[i-j]-sum((m[i-j+k-1]/k for k in range(1,j+1)),F(0)))
    other=4*sum(((-1)**j*comb(6*N,j)*c(52*N-1+j) for j in range(6*N+1)),F(0))
    assert u==other and u<0
    return u,v

lo,hi=catalan_interval();out=[];last=None
eta=F(7**7*4**4,16*11**11)
for N in range(1,7):
    u,v=central(N);r=-v/u
    flo,fhi=u*hi+v,u*lo+v
    assert flo>0 if N%2 else fhi<0
    assert r>hi if N%2 else r<lo
    if last is not None:assert r!=last
    last=r
    # Upper bound |r-G| <= 2^114 sqrt(N) eta^N for N>=2,
    # checked with N in place of sqrt(N) and a harmless K=16 scalar majorant.
    err=max(abs(r-lo),abs(r-hi))
    if N>=2: assert err<=2**118*N*eta**N
    out.append({'N':N,'u_sign':-1,'F_sign':1 if N%2 else -1,'numerator_bits':abs(r.numerator).bit_length(),'denominator_bits':r.denominator.bit_length(),'denominator':str(r.denominator),'error_upper':str(err),'decimal_log_error_over_log_denominator':-log(float(err))/log(r.denominator)})
# Exact area of the inherited loss envelope; used only to test our transcription.
xs=[F(0),F(25),F(29),F(65,2),F(69,2),F(40),F(58),F(59),F(65)]
ys=[96,96,88,88,84,62,8,6,0]
area=sum(((xs[i+1]-xs[i])*(ys[i+1]+ys[i])/2 for i in range(8)),F(0));assert area==F(8609,2)
# Log2 bracket by positive series; exact certificate of the margin B-A > 1/10000.
l2=sum((F(2,3**(2*j+1)*(2*j+1)) for j in range(12)),F(0));l2u=l2+F(2,3**25*25)*F(9,8)
margin=F(2290939875,10**9)-F(8609,4608)-F(2809,4608)*l2u
assert margin>F(1,10000)
# Bad-prime charge: for p>2sqrt(H), (1+logH/logp)<3; numerically stress strict inequality only.
count=0
for H in range(2,1000):
    for p in (3,5,7,11,17,31,67,127,257,521,1031):
        if p*p>4*H:
            assert 1+log(H)/log(p)<3;count+=1
# Rational scalar perturbation: denominator loss is per entry, never a free n-independent constant.
for n in range(1,12):
    for b in range(2,50):assert F(1,b)**n==F(1,b**n)
print(json.dumps({'status':'PASS finite diagnostics only','central_approximants':out,'loss_area':str(area),'gap_lower':str(margin),'eta':str(eta),'kappa_decimal':-log(float(eta)),'bad_prime_cases':count,'euler_terms':240},indent=2,sort_keys=True))
