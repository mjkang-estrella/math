#!/usr/bin/env python3
"""Independent finite certificate; standard library only; prints JSON, writes nothing."""
from math import factorial, prod
from fractions import Fraction
import json
from datetime import datetime, timezone
A=(3,5,6,7,8,14,16,20,36)
B=(4,10,12,15,18,21,32)
assert len(A)==len(set(A))==9 and len(B)==len(set(B))==7
assert set(A).isdisjoint(B) and min(A+B)>1
primes=[p for p in range(2,max(A+B)+1) if all(p%d for d in range(2,p))]
def valuation_factor(x,p):
    n=0
    while x%p==0:
        n+=1; x//=p
    return n
def legendre(t,p):
    s=0; q=p
    while q<=t:
        s+=t//q; q*=p
    return s-t*valuation_factor(t,p)
def trial(t,p):
    return sum(valuation_factor(i,p) for i in range(1,t+1))-t*valuation_factor(t,p)
rows=[]
for p in primes:
    assert all(legendre(t,p)==trial(t,p) for t in A+B)
    a=sum(legendre(t,p) for t in A); b=sum(legendre(t,p) for t in B)
    assert a==b; rows.append([p,a,b])
numA=prod(factorial(t) for t in A); denA=prod(t**t for t in A)
numB=prod(factorial(t) for t in B); denB=prod(t**t for t in B)
lhs=numA*denB; rhs=numB*denA
assert lhs==rhs
ra=prod((Fraction(factorial(t),t**t) for t in A),start=Fraction(1))
rb=prod((Fraction(factorial(t),t**t) for t in B),start=Fraction(1))
assert ra==rb
expected=Fraction(11**6*13**5*17**3*19**2*23*29*31,2**123*3**37*5**4*7**8)
assert ra==expected
print(json.dumps(dict(utc=datetime.now(timezone.utc).isoformat(),verdict="PASS",A=A,B=B,cardinalities=[len(A),len(B)],valuations=rows,individual_entries_checked=len(A+B)*len(primes),cross_product_digits=len(str(lhs)),cross_product=str(lhs),common_rational=str(ra),higher_primes_zero_reason="All prime factors of t! and t^t are <=t<=36"),indent=2))
