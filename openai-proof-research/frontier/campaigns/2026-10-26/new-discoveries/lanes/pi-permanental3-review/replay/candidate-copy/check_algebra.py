#!/usr/bin/env python3
"""Exact independent determinant/permanent expansions, not a novelty certificate."""
from itertools import permutations, combinations
from pathlib import Path
import json, random
import sympy as s

x,b,c,d,t,e=s.symbols('x b c d t e',positive=True)
def per(A):
    n=A.rows
    return s.expand(sum(s.prod(A[i,p[i]] for i in range(n)) for p in permutations(range(n))))
def ratio(A):
    return s.cancel(per(A.extract([0,1],[0,1]))*per(A.extract([1,2],[1,2]))/(per(A)*A[1,1]))
def minors(A):
    return [s.factor(A.extract(I,J).det()) for k in range(1,4)
            for I in combinations(range(3),k) for J in combinations(range(3),k)]

w=x+b+c+b*c/(x-1)+d
A=s.Matrix([[1,1,1],[1,x,x+b],[1,x+c,w]])
N=s.expand(per(A.extract([0,1],[0,1]))*per(A.extract([1,2],[1,2])))
D=s.expand(per(A)*A[1,1])
assert s.factor(N-D-(b*c-2*x*x))==0
assert s.factor(A.det()-(x-1)*d)==0
low=2*x*x*(x-1)**2+2*x*(x+1)*(x-1)*(b+c)+(2*x*x+3*(x-1))*b*c+x*(x+1)*(x-1)*d
high=2*x**3*(x-1)+20*x*x*(x-1)+2*x*(x+1)*(x-1)*(b+c)+2*(x-2)**2*b*c+x*(x+1)*(x-1)*d
assert s.factor((x-1)*(3*N-2*D)-low)==0
assert s.factor((x-1)*(9*D-8*N)-high)==0
U=s.Matrix([[1,1,1],[1,2,t+2],[1,t+2,t*t+2*t+3]])
L=s.Matrix([[1,1,1],[1,1+e,1+2*e],[1,1+2*e,1+5*e]])
assert all(q.is_positive for q in minors(U))
assert all(q.is_positive for q in minors(L))
ru=ratio(U);rl=ratio(L)
assert s.limit(ru,t,s.oo)==s.Rational(9,8)
assert s.limit(rl,e,0,dir='+')==s.Rational(2,3)
small=U.subs(t,7)
assert ratio(small)>s.Rational(121,114)
rng=random.Random(20261026)
for _ in range(1000):
    vals={x:1+s.Rational(rng.randrange(1,100),rng.randrange(1,20)),
          b:s.Rational(rng.randrange(1,100),rng.randrange(1,20)),
          c:s.Rational(rng.randrange(1,100),rng.randrange(1,20)),
          d:s.Rational(rng.randrange(1,100),rng.randrange(1,20))}
    M=A.subs(vals)
    assert all(q>0 for q in minors(M))
    assert s.Rational(2,3)<ratio(M)<s.Rational(9,8)
result={'status':'PASS exact algebra','credit':0,'universal_normalized_lower_certificate':str(s.factor(low)),
        'universal_normalized_upper_certificate':str(s.factor(high)),
        'upper_family_ratio':str(ru),'upper_family_minors':list(map(str,minors(U))),
        'lower_family_ratio':str(rl),'lower_family_minors':list(map(str,minors(L))),
        'upper_limit':'9/8','lower_limit':'2/3','small_integer_matrix':[[int(v) for v in row] for row in small.tolist()],
        'small_integer_ratio':str(ratio(small)),'random_exact_TP_checks':1000,
        'qualification':'No Lean endpoint or serious independent novelty review yet; not accepted.'}
print(json.dumps(result,indent=2))
