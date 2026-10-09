"""Exact finite diagnostics. These do not establish CR or any asymptotic."""
from array import array
from fractions import Fraction
from itertools import product
from math import gcd, isqrt, prod, log
from pathlib import Path
import json

OUT = Path(__file__).parent
LIMIT = 2_000_000
largest = array('I', [0]) * (LIMIT + 1)
primes = []
for q in range(2, LIMIT + 1):
    if largest[q] == 0:
        primes.append(q)
        for n in range(q, LIMIT + 1, q):
            largest[n] = q

def tr(e):
    return 2 if e % 3 == 0 else -1

table = []
for s, t in product(range(3), repeat=2):
    ts = [tr(s), tr(t), tr(s+t), tr(2*s+t)]
    z = ts[1] + ts[3] - 2*ts[0] - 2*ts[2]
    good = s != 0 and (s+t) % 3 != 0
    assert 4 + z == 9*good
    table.append(dict(s=s, t=t, traces_2_3_6_12=ts, B=z, good=good))
assert sum(row['good'] for row in table) == 4
assert sum(row['B'] for row in table) == 0
# Norm geometry does not preserve the rational predecessor shift.
norm_dilation_checks=0
for q in (5,7,13,19):
    for a,b in product(range(-4,5),repeat=2):
        nz=a*a-a*b+b*b
        assert q*q*nz-1-q*q*(nz-1)==q*q-1
        norm_dilation_checks+=1

# The generalized dihedral group, multiplication (v,e)(w,f)=(v+(-1)^e w,e+f).
elts = [(a,b,e) for a,b,e in product(range(3),range(3),range(2))]
def mul(g,h):
    a,b,e=g; c,d,f=h
    return ((a+(-1)**e*c)%3,(b+(-1)**e*d)%3,(e+f)%2)
def inv(g):
    return next(h for h in elts if mul(g,h)==(0,0,0))
comm = {mul(mul(mul(g,h),inv(g)),inv(h)) for g,h in product(elts,repeat=2)}
assert comm == {(s,t,0) for s,t in product(range(3),repeat=2)}
classes = {tuple(sorted(mul(mul(h,g),inv(h)) for h in elts)) for g in elts}

def primary_generators(p):
    out = []
    for b in range(-isqrt(4*p//3)-1,isqrt(4*p//3)+2):
        d = 4*p-3*b*b
        if d < 0: continue
        r = isqrt(d)
        if r*r != d: continue
        for z in set([r,-r]):
            if (b+z)%2: continue
            a=(b+z)//2
            if a%3==1 and b%3==0:
                assert a*a-a*b+b*b==p
                out.append((a,b))
    assert len(out)==2, (p,out)
    return out

ray_labels = {}
norm_labels = {}
ray_checks = trace_checks = 0
norm_witness = None
for p in primes:
    if p > 100_000: break
    if p <= 3 or p%3!=1: continue
    traces = [2 if pow(a,(p-1)//3,p)==1 else -1 for a in (2,3,6,12)]
    B = traces[1]+traces[3]-2*traces[0]-2*traces[2]
    good = pow(2,(p-1)//3,p)!=1 and pow(-6,(p-1)//3,p)!=1
    assert 4+B==9*good
    trace_checks += 1
    labels = []
    for a,b in primary_generators(p):
        omega=(-a*pow(b,-1,p))%p
        assert omega!=1 and (omega*omega+omega+1)%p==0
        powers={pow(omega,j,p):j for j in range(3)}
        s,t=[powers[pow(k,(p-1)//3,p)] for k in (2,3)]
        key=(a%72,b%72)
        assert ray_labels.setdefault(key,(s,t))==(s,t)
        labels.append((s,t))
        ray_checks+=1
        nk=p%72
        data=dict(p=p,generator=[a,b],label=[s,t],good=good)
        if p%24 in (13,19) and nk in norm_labels and norm_labels[nk]['good']!=good and norm_witness is None:
            norm_witness=[norm_labels[nk],data]
        norm_labels.setdefault(nk,data)
    # Rational principal ideals (p)=pi*conj(pi) have trivial cubic character.
    assert all((labels[0][j]+labels[1][j])%3==0 for j in range(2))

stats=[]
for x in (100_000,500_000,1_000_000):
    dyad=[p for p in primes if x<p<=2*x]
    for b in (13,19):
        for Y in (3,5,7,11):
            qs=[q for q in (5,7,11) if q<=Y]
            w=Fraction(1,8)*prod((Fraction(q-2,q-1) for q in qs),start=Fraction(1))
            ap=[p for p in dyad if p%24==b and all(p%q!=1 for q in qs)]
            for den in (4,10):
                reservoir=[p for p in ap if largest[p-1]**den>x**(den-1)]
                good=0; Bsum=0
                for p in reservoir:
                    traces=[2 if pow(a,(p-1)//3,p)==1 else -1 for a in (2,3,6,12)]
                    B=traces[1]+traces[3]-2*traces[0]-2*traces[2]
                    flag=pow(2,(p-1)//3,p)!=1 and pow(-6,(p-1)//3,p)!=1
                    good+=flag; Bsum+=B
                assert 9*good==4*len(reservoir)+Bsum
                stats.append(dict(x=x,b=b,Y=Y,theta=f'1/{den}',modulus=24*prod(qs),weight=str(w),all_dyad_primes=len(dyad),AP_count=len(ap),reservoir=len(reservoir),good=good,B_sum=Bsum))

# Independent small-prime-union count, including all compatible residue classes.
crt=[]
for Y in (3,5,7,11):
    qs=[q for q in (5,7,11) if q<=Y]; M=24*prod(qs)
    phi=sum(gcd(b,M)==1 for b in range(M))
    for b0 in (13,19):
        count=sum(gcd(b,M)==1 and b%24==b0 and all(b%q!=1 for q in qs) for b in range(M))
        w=Fraction(1,8)*prod((Fraction(q-2,q-1) for q in qs),start=Fraction(1))
        assert Fraction(count,phi)==w
        crt.append(dict(Y=Y,b=b0,M=M,classes=count,phi=phi,weight=str(w)))

# Completely multiplicative extension f(ell)=trace_2(ell)/2 cannot be stripped.
def f(n):
    out=Fraction(1)
    while n>1:
        p=largest[n];n//=p
        tp=2 if p in (2,3) else (0 if p%3==2 else (2 if pow(2,(p-1)//3,p)==1 else -1))
        out*=Fraction(tp,2)
    return out
stripping=[]
for ell in (7,13,19,31,37,43):
    for w in (1,2,3,6,12,18):
        if ell*(w+1)>LIMIT: continue
        assert f(ell*(w+1))==f(ell)*f(w+1)
        if f(ell*(w+1))!=f(w+1):
            stripping.append(dict(active_prime=ell,w=w,unstripped=str(f(ell*(w+1))),stripped=str(f(w+1))))
assert stripping and norm_witness

result=dict(scope='Finite exact algebra and diagnostics only; theta=1/4 and 1/10 are NOT the required theta<1e-6.',group_order=len(elts),commutator_order=len(comm),conjugacy_class_count=len(classes),fourier_table=table,prime_trace_checks=trace_checks,oriented_ray_checks=ray_checks,occupied_ray_classes=len(ray_labels),norm_dilation_checks=norm_dilation_checks,norm_residue_counterexample=norm_witness,crt=crt,stripping_counterexamples=stripping[:8],reservoir_statistics=stats,tiny_theta_lower_log_x=log(3)/1e-6,failures=0)
(OUT/'independent-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('reservoir_statistics','fourier_table','crt')},indent=2))
