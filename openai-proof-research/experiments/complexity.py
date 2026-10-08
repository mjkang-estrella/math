"""Exact exponent checks and algebraic checks; no timing/novelty claims."""
from fractions import Fraction as Q
import random

MOD = 1000003

def mm(a, b):
    return [[sum(x*y for x, y in zip(row, col)) % MOD
             for col in zip(*b)] for row in a]

def transpose(a):
    return [list(row) for row in zip(*a)]

def ident(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]

def add(a, b, sign=1):
    return [[(x+sign*y) % MOD for x,y in zip(u,v)] for u,v in zip(a,b)]

def inv(a):
    n=len(a)
    b=[list(row)+list(unit) for row,unit in zip(a,ident(n))]
    for j in range(n):
        pivot=next((i for i in range(j,n) if b[i][j]),None)
        if pivot is None:
            raise ValueError('singular')
        b[j],b[pivot]=b[pivot],b[j]
        scale=pow(b[j][j],-1,MOD)
        b[j]=[x*scale % MOD for x in b[j]]
        for i in range(n):
            if i != j:
                factor=b[i][j]
                b[i]=[(x-factor*y) % MOD for x,y in zip(b[i],b[j])]
    return [row[n:] for row in b]

for r in range(4,11):
    p=Q(r-2,r-1)
    q=Q(r-2,2*r-3)
    ell=Q(1,2*r-3)
    assert q == p*(1-q)
    assert ell-1 == -2*q
    assert -p*(ell+1) == -2*q
    assert 1/q == Q(2*r-3,r-2)
    # Older D*loglog(D)/log(D) introduces a (loglog m)^q loss.
    assert 1-Q(1,1+p) == q
    print(f'r={r}: edge-color exponent {q}; minimum-edge exponent {1/q}; log exponent 2')

rng=random.Random(107184)
for case in range(40):
    n=7+case % 5
    h=1+case % 3
    s=rng.sample(range(n),h)
    a=[[0]*n for _ in range(n)]
    for i in range(n):
        for j in range(i):
            a[i][j]=a[j][i]=rng.randrange(2)
    ap=[row[:] for row in a]
    for i in range(n):
        for j in range(i):
            if (i in s or j in s) and rng.randrange(2):
                ap[i][j]=ap[j][i]=1-a[i][j]
    d=add(ap,a,-1)
    selector=[[int(i==j) for j in s] for i in range(n)]
    b=mm(transpose(selector),d)
    c=mm(d,selector)
    for i in s:
        c[i]=[0]*h
    u=[x+y for x,y in zip(selector,c)]
    vt=b+transpose(selector)
    assert mm(u,vt)==d
    z=7
    x=[[(-z*v) % MOD for v in row] for row in u]
    m=add(ident(n),[[z*v % MOD for v in row] for row in a],-1)
    mp=add(ident(n),[[z*v % MOD for v in row] for row in ap],-1)
    old=inv(m)
    small=add(ident(2*h),mm(mm(vt,old),x))
    updated=add(old,mm(mm(mm(mm(old,x),inv(small)),vt),old),-1)
    assert updated == inv(mp)
print('PASS: exact exponent balancing and 40 hub-factor/Woodbury checks')
