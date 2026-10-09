"""Finite checks of the NEW residue-lifting algebra, never of asymptotic contracts."""
from fractions import Fraction
from math import gcd, isqrt, prod
from pathlib import Path
import json, cmath
def primerange(lo, hi):
    sieve=bytearray(b'\1')*hi
    if hi>0: sieve[0]=0
    if hi>1: sieve[1]=0
    for q in range(2,isqrt(hi-1)+1):
        if sieve[q]: sieve[q*q:hi:q]=b'\0'*((hi-1-q*q)//q+1)
    return [q for q in range(max(2,lo),hi) if sieve[q]]
def factorint(n):
    out={};q=2
    while q*q<=n:
        while n%q==0: out[q]=out.get(q,0)+1;n//=q
        q+=1
    if n>1:out[n]=out.get(n,0)+1
    return out
def kronecker_symbol(a,n):
    assert n>0 and n%2
    a%=n;sign=1
    while a:
        while a%2==0:
            a//=2
            if n%8 in (3,5):sign=-sign
        a,n=n,a
        if a%4==n%4==3:sign=-sign
        a%=n
    return sign if n==1 else 0
OUT=Path(__file__).resolve().parent
stats={}
# Count exactly, allowing nonunit source residue r, including prime-power moduli.
cases=0
nonunit_source=0
for M in range(2,49):
    units=[t for t in range(M) if gcd(t,M)==1]
    for d in units:
        for w in range(M):
            counts=[0]*M
            for t in units:
                r=t*w%M
                if t*(w+d)%M==(r+1)%M: counts[r]+=1
            for r in range(M):
                assert counts[r]==int((w-r*d)%M==0),(M,d,w,r,counts[r])
                cases+=1;nonunit_source+=gcd(r,M)>1
stats['shared_dilation_identity']={'cases':cases,'nonunit_source_cases':nonunit_source,'failures':0}
# A single endpoint does not recover source progression, and naively invariant core fails.
M=5;w=1;r=2
stats['single_endpoint_failure']={'M':M,'r':r,'w':w,'averaged_mass':str(Fraction(sum(t*w%M==r for t in range(1,M)),M-1)),'desired_indicator':int(w==r)}
stats['core_invariance_failure']={'M':3,'target':1,'n':1,'active_prime':5,'indicator_n':1,'indicator_active_times_n':0}
# Restriction is multiplication in physical space / translation in Fourier space.
maxerr=0.;nchecks=0
for M in range(2,31):
    arr=[complex((7*n*n+2*n)%19-9,(3*n)%5-2) for n in range(2*M+5)]
    for r in range(M):
        for theta in [Fraction(1,7),Fraction(2,9),Fraction(3,16)]:
            lhs=sum(a*cmath.exp(2j*cmath.pi*float(theta*n)) for n,a in enumerate(arr) if n%M==r)
            rhs=sum(cmath.exp(-2j*cmath.pi*j*r/M)*sum(a*cmath.exp(2j*cmath.pi*(float(theta)+j/M)*n) for n,a in enumerate(arr)) for j in range(M))/M
            maxerr=max(maxerr,abs(lhs-rhs));nchecks+=1
assert maxerr<1e-8
stats['periodic_Fourier_identity']={'cases':nchecks,'max_abs_error':maxerr}
# Uniform unit factor times an arbitrary independent unit factor is uniform.
cc=0
for M in range(2,65):
    units=[u for u in range(M) if gcd(u,M)==1];den=sum(range(1,len(units)+1))
    law={u:Fraction(i+1,den) for i,u in enumerate(units)}
    conv={r:sum(law[v]/len(units) for u in units for v in units if u*v%M==r) for r in units}
    assert all(v==Fraction(1,len(units)) for v in conv.values());cc+=1
stats['uniform_multiplicative_convolution']={'moduli':cc,'failures':0}
# Construct the admissible quadratic class for signed bases and perfect powers.
basecases=[]
for a in range(-100,101):
    if abs(a)<2 or (a>=0 and isqrt(a)**2==a): continue
    odd=[int(q) for q in factorint(abs(a)) if q!=2]
    M=8*prod(odd)
    u=next(u for u in range(1,M,2) if gcd(u,M)==1 and u%8 in [3,5,7] and all(u%q!=1 for q in odd) and kronecker_symbol(a,u)==-1)
    tested=[int(p) for p in primerange(3,20000) if p%M==u]
    assert all(a%p and pow(a%p,(p-1)//2,p)==p-1 for p in tested)
    basecases.append({'a':a,'M':M,'u':u,'primes_checked':len(tested)})
stats['quadratic_classes']={'bases':len(basecases),'prime_instances':sum(x['primes_checked'] for x in basecases),'cases':basecases,'failures':0}
# Entanglement example: class p=1 mod5 forces 5 to be a square, despite being reduced.
ps=[int(p) for p in primerange(7,10000) if p%5==1]
assert all(pow(5,(p-1)//2,p)==1 for p in ps)
stats['local_entanglement_counterexample']={'base':5,'modulus':5,'class':1,'primes_checked':len(ps),'all_quadratic_residues':True}
# All-class reservoir weights, not one chosen class; exact CRT check on small Y.
rows=[]
for Y in [3,5,7,11,13]:
    M0=8;u0=3;qs=list(primerange(3,Y+1));M=M0*prod(qs)
    w=Fraction(1,4)*prod(Fraction(q-2,q-1) for q in qs)
    if M<=300000:
        count=sum(gcd(v,M)==1 and v%8==u0 and all(v%q!=1 for q in qs) for v in range(M))
        phi=4*prod(q-1 for q in qs)
        assert Fraction(count,phi)==w
    rows.append({'Y':Y,'M':M,'union_prime_density':str(w),'one_class_density':str(Fraction(1,4*prod(q-1 for q in qs))),'Y_times_union_density':float(Y*w)})
stats['union_density']=rows
(OUT/'results.json').write_text(json.dumps(stats,indent=2)+'\n')
print(json.dumps({k:({kk:vv for kk,vv in v.items() if kk!='cases'} if isinstance(v,dict) else v) for k,v in stats.items()},indent=2))
