"""Independent exact controls; no candidate checker imported. Not a proof."""
from math import comb, factorial
from fractions import Fraction as F
from pathlib import Path
import json, datetime

def c(a,b):
    assert a >= 0
    return comb(a,b) if 0 <= b <= a else 0
def p(r,i,k): return c(k,i)*c(k+r+i-1,i)
def a(r,i,j,l):
    return c(l,i)*c(l,j)*c(r+i+j-1,i+j-l) if l>=0 else 0
def s(r,l,n):
    if n==0 or l>=n: return 0
    return (n+r-1)*c(n,l+1)*c(n+r+l-1,l)
def vp(n,p):
    assert n>0
    v=0
    while n%p==0:n//=p;v+=1
    return v
counts={}
def check(kind,b):
    assert b,kind
    counts[kind]=counts.get(kind,0)+1

for r in [1,2,3,4,8,9,12,25,27,32,72]:
    for i in range(11):
        for j in range(11):
            for l in range(i+j+4):
                check('recurrence', (j+1)**2*a(r,i,j+1,l)==l*l*a(r,i,j,l-1)+(l*(l+r)-j*(j+r))*a(r,i,j,l))
            for k in [0,1,2,7,12,35,101]:
                check('linearization',p(r,i,k)*p(r,j,k)==sum(a(r,i,j,l)*p(r,l,k) for l in range(i+j+1)))
    for l in range(36):
        running=0
        for n in range(81):
            check('telescoping',running==s(r,l,n))
            running+=(2*n+r)*p(r,l,n)

# Independently integrate coefficient polynomials using exact beta moments.
for r in [1,2,4,9,25]:
    for k in range(9):
        for h in range(k+1):
            inner=sum(F((-1)**(i+j)*p(r,i,k)*p(r,j,h),c(i+j+r,r)) for i in range(k+1) for j in range(h+1))
            check('jacobi_norm',inner==(F(r,2*k+r) if k==h else 0))

def invert(mat):
    n=len(mat);t=[row[:]+[F(i==j) for j in range(n)] for i,row in enumerate(mat)]
    for i in range(n):
        q=next(j for j in range(i,n) if t[j][i]);t[i],t[q]=t[q],t[i]
        z=t[i][i];t[i]=[v/z for v in t[i]]
        for j in range(n):
            if j!=i:
                z=t[j][i];t[j]=[x-z*y for x,y in zip(t[j],t[i])]
    return [row[n:] for row in t]
for r in list(range(1,41))+[64,72,81,100,125,144]:
    for n in range(1,10):
        inv=invert([[F(1,c(i+j+r,r)) for j in range(n)] for i in range(n)])
        check('integrality_iff',all(x.denominator==1 for row in inv for x in row)==(n*(n-1)%r==0))
        for i in range(n):
            for j in range(n):
                kernel=F((-1)**(i+j)*sum((2*k+r)*p(r,i,k)*p(r,j,k) for k in range(n)),r)
                check('inverse_entry',kernel==inv[i][j])

# Includes l >> p^e and n >> p^e, both residue branches, r with extra factors.
for prime,e in [(2,1),(2,2),(2,7),(3,2),(3,4),(5,3),(7,2),(11,2)]:
    q=prime**e
    for mult in [1,2,5]:
        r=q*mult
        for n in [q,q+1,3*q,3*q+1,19*q,19*q+1]:
            for m in sorted({1,2,q-1,q,q+1,2*q,n//2,n-1,n,n+1}):
                if not 1<=m<=n:continue
                check('prime_power_sum',s(r,m-1,n)%q==0)
                if n%q==0:
                    t=vp(m,prime);z=min(e,t)
                    check('valuation_split',vp(c(n,m),prime)>=max(0,e-t) and vp(c(n+r+m-2,m-1),prime)>=z)
# Mixed CRT: n need not be 0 or 1 modulo r itself.
for r,n in [(72,9),(72,64),(100,25),(100,76),(225,100),(225,126)]:
    check('mixed_crt_hypothesis',n*(n-1)%r==0 and n%r not in [0,1])
    for l in range(n+3):check('mixed_crt_sums',s(r,l,n)%r==0)
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','counts':counts,'scope':'Finite exact rational/integer controls only; universal argument in review.md.'}
Path(__file__).with_name('check-results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
