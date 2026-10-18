#!/usr/bin/env python3
"""MIT. Exact integer checks only; topology and reconstruction are not simulated."""
import json
from math import isqrt

def mul(x,y):
    a,b=x;c,d=y
    return a*c+b*d,a*d+b*c+b*d

def power(x,n):
    z=(1,0)
    while n:
        if n&1:z=mul(z,x)
        x=mul(x,x);n//=2
    return z

def norm(z):
    a,b=z
    return a*a+a*b-b*b

def lucas(n):
    a,b=2,1
    for _ in range(n):a,b=b,a+b
    return a

def fib(n):
    a,b=0,1
    for _ in range(n):a,b=b,a+b
    return a

def square(n):return n>=0 and isqrt(n)**2==n

def prime_factors(n):
    d=2
    while d*d<=n:
        if n%d==0:
            yield d
            while n%d==0:n//=d
        d+=1
    if n>1:yield n

def tau_order(q):
    z=(1,0)
    for k in range(1,q*q+1):
        a,b=mul(z,(0,1));z=(a%q,b%q)
        if z==(1,0):return k
    raise AssertionError('unit order not found')

modular=[]
for m in range(2,81):
    q=next(q for q in prime_factors(4*(m-1)-1) if q%4==3)
    assert (m-1)%q
    r=tau_order(q);b=r
    while m*m+1-m*lucas(2*b)>=0:b+=r
    N=m*m+1-m*lucas(2*b)
    # tau^-2 = 2-tau, independently check the norm formula.
    a,c=power((2,-1),b)
    assert norm((m-a,-c))==N
    assert N%q==((m-1)**2)%q
    assert pow((-N)%q,(q-1)//2,q)==q-1
    assert not square(-N)
    modular.append(dict(m=m,q=q,order=r,b=b,norm=N))
for b in range(2,82,2):
    assert lucas(2*b)-2==5*fib(b)**2
    assert not square(lucas(2*b)-2)
square_tail=[]
for r in range(2,16):
    m=r*r;checked=0
    for b in range(1,121):
        x=r*lucas(b);C=(m+(-1)**b)**2
        assert m*lucas(2*b)-m*m-1==x*x-C
        if 0<C<2*x-1:
            assert (x-1)**2<x*x-C<x*x
            assert not square(x*x-C)
            checked+=1
    assert checked
    square_tail.append(dict(m=m,checked=checked))
B=[3]
for d in range(1,9):B.append(d+3+(d+1)*B[-1])
connectivity=[]
for m in range(1,21):
    for d in range(9):
        b=1
        while m*(lucas(2*b)-1)<=max(B[d],11*(d+2)):b+=1
        connectivity.append(dict(m=m,d=d,b=b,vertex_bound=B[d]))
print(json.dumps({'status':'PASS','limits':'Integer identities and explicit parameter witnesses only; no proof of group finiteness.','modular_witnesses':modular,'m1_even_examples':40,'square_tail_checks':square_tail,'connectivity_parameter_witnesses':connectivity},indent=2))
