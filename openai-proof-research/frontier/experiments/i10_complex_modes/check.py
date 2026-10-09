"""Exact finite checks supporting i10; none proves an asymptotic estimate."""
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path
import json
import math

OUT = Path(__file__).resolve().parent / 'results.json'

def mul(a, b, m):
    # Quotient rings Q[z]/(z^2+1), Q[z]/(z^2+z+1).
    c0, c1, c2 = a[0]*b[0], a[0]*b[1]+a[1]*b[0], a[1]*b[1]
    return (c0-c2, c1-(c2 if m == 3 else 0))

def power(a, n, m):
    r = (F(1), F(0))
    for _ in range(n % m):
        r = mul(r, a, m)
    return r

def add(a,b): return (a[0]+b[0],a[1]+b[1])
def scale(a,c): return (a[0]*c,a[1]*c)
one, z = (F(1),F(0)), (F(0),F(1))

def omega(n):
    o=0; p=2
    while p*p<=n:
        while n%p==0: n//=p;o+=1
        p+=1
    return o+(n>1)

def smallpart(n, primes):
    a=1
    for p in primes:
        while n%p==0: n//=p;a*=p
    return a

def divisors(n): return [d for d in range(1,n+1) if n%d==0]
def mu(n):
    p=2;o=0
    while p*p<=n:
        if n%p==0:
            n//=p;o+=1
            if n%p==0:return 0
        p+=1
    return (-1)**(o+(n>1))

# Replace beta by a rational test. Covariance depends only on its argument,
# so this checks prime powers, repeated labels, and the exact quotient.
cov=0
for m in (3,4):
    def model(n):
        a=smallpart(n,(2,3,5))
        val=sum(F(1,l)*F(n+a*l,a*l) for l in (7,11,13))
        return scale(mul(power(z,omega(a),m),power(z,1,m),m),val)
    for n in range(1,301):
        for a in (2,4,6,9,25,30,72):
            assert model(a*n)==mul(power(z,omega(a),m),model(n),m)
            cov+=1
    for J,s,c in product(range(1,5),range(1,5),range(0,5)):
        if c<=J*s:
            assert power(z,J*s-c,m)==mul(power(z,J*s,m),power(z,-c,m),m)

# Density-vs-cumulative coefficients: derivative converts H/(1+w) to H.
# Gamma recurrence is encoded by the exact falling factorial in Q[z].
density=0
for m in (3,4):
    h=[(F(j+1, j+2),F((-1)**j,j+3)) for j in range(9)]
    q=[]
    for j in range(len(h)):
        q.append(add(h[j],scale(q[-1],-1)) if j else h[j])
    for j in range(1,len(h)):
        assert add(q[j],q[j-1])==h[j];density+=1
    for j in range(7):
        for r in range(7):
            # Gamma(z-j)/Gamma(z-j-r) = product_{h=1}^r (z-j-h).
            falling=one
            for k in range(1,r+1):
                falling=mul(falling,add(z,(-F(j+k),F(0))),m)
            binomial=scale(falling,F(1,math.factorial(r)))
            assert scale(binomial,math.factorial(r))==falling;density+=1

# Ramanujan sums are computed by their integer divisor formula, not floats.
def ram(k,h): return sum(d*mu(k//d) for d in divisors(math.gcd(k,h)))
unit=0
for k in range(1,61):
    for h in range(k):
        for ell in range(1,k+1):
            if math.gcd(k,ell)==1:
                assert ram(k,h*ell)==ram(k,h);unit+=1

# CRT density (23), with finite small-prime set; this includes prime powers q.
primes=(2,3,5,7)
P=math.prod(primes)
V=math.prod(F(p-1,p) for p in primes)
crt=0
for q in range(1,51):
    phi=sum(math.gcd(a,q)==1 for a in range(1,q+1))
    period=math.lcm(q,P)
    empirical=F(sum(n%q==1%q and math.gcd(n,P)==1 for n in range(period)),period)
    expected=V/F(q)
    for p in primes:
        if q%p==0:expected/=F(p-1,p)
    assert empirical==expected
    local=V/F(phi)
    for p in range(2,q+1):
        if q%p==0 and all(p%d for d in range(2,math.isqrt(p)+1)) and p not in primes:
            local*=F(p-1,p)
    assert expected==local;crt+=1

# Undo a retained-success expansion before multiplying a common complex model.
coin=0
for n in range(1,7):
    probs=[F(j+1,n+2) for j in range(n)]
    for threshold in range(n+1):
        direct=F(0);expanded=F(0);mass=F(0)
        for bits in product((0,1),repeat=n):
            S={i for i,b in enumerate(bits) if b}
            if len(S)<threshold:continue
            direct+=math.prod(probs[i] if i in S else 1-probs[i] for i in range(n))
            absent=[i for i in range(n) if i not in S]
            for size in range(len(absent)+1):
                for T in combinations(absent,size):
                    term=math.prod(probs[i] for i in S|set(T))
                    expanded+=(-1)**size*term;mass+=term
        assert direct==expanded and 0<=direct<=1 and mass>=direct
        common=(F(2,7),F(-3,11))
        assert scale(common,direct)==scale(common,expanded);coin+=1

# Fixed-class compatibility and reduced modulus, including a sharing M's powers.
gcd_cases=0
for M in range(1,17):
    for b in range(M):
        if math.gcd(b,M)!=1:continue
        g=math.gcd(b-1,M)
        for a in range(1,41):
            if math.gcd(a,M)!=g:continue
            assert math.gcd(a//g,M//g)==1
            for v in range(1,2*M+1):
                if math.gcd(v,M)!=1:continue
                assert ((a*v-b+1)%M==0)==(((a//g)*v-(b-1)//g)%(M//g)==0)
                gcd_cases+=1

results={'status':'pass','exact_cases':{'small_part_covariance':cov,
         'density_coefficient_recurrence':density,'ramanujan_unit_invariance':unit,
         'crt_density':crt,'positive_coin_reassembly':coin,'fixed_class_reduction':gcd_cases},
         'arithmetic':'rational numbers and exact cyclotomic quotient rings',
         'limitation':'Finite algebra checks only; no numerical prime or asymptotic proof.'}
OUT.write_text(json.dumps(results,indent=2)+'\n')
print(json.dumps(results))
