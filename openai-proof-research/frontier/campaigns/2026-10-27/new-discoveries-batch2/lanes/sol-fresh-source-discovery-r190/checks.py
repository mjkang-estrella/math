from fractions import Fraction as F
from itertools import combinations
from math import gcd,lcm
import random,json

def probability(A):
    # t=x/(2*pi); all zeros are (2k+1)/(4a).
    events={}
    for i,a in enumerate(A):
        for k in range(2*a):
            t=F(2*k+1,4*a)
            events[t]=events.get(t,0)^(1<<i)
    mask=0;full=(1<<len(A))-1;last=F(0);p=F(0)
    for t,flip in sorted(events.items()):
        if mask in (0,full):p+=t-last
        mask^=flip;last=t
    if mask in (0,full):p+=1-last
    return p

def grid(A):
    # Independent source Lemma 2.2 implementation, bounded lcm only.
    q=lcm(*A);assert q<=50000
    good=0
    for j in range(4*q):
        signs=[((a*(2*j+1)+2*q)//(4*q))%2 for a in A]
        good+=len(set(signs))==1
    return F(good,4*q)

controls=[(1,3),(1,3,9),(1,3,11,33),(1,3,4,12),(2,4,5,15),(1,3,11,35,105),(1,7,11,33,99)]
rows=[]
for A in controls:
    p=probability(A);assert grid(A)==p
    rows.append(dict(A=A,P=str(p)))
assert probability(controls[5])==F(1,105)
assert probability(controls[6])==F(1,99)
best=(F(1),None);count=0
for b in range(5,42,2):
    for c in range(b+2,82,2):
        A=(1,3,b,c,3*c);p=probability(A);count+=1
        if p<best[0]:best=(p,A)
rng=random.Random(190);random_min=(F(1),None)
for _ in range(500):
    A=tuple(sorted(rng.sample(range(1,301),5)));p=probability(A)
    if p<random_min[0]:random_min=(p,A)
    # Exact indicator expansion at every sign pattern, independent of source.
for bits in range(32):
    signs=[1 if bits>>i&1 else -1 for i in range(5)]
    pair=sum(signs[i]*signs[j] for i,j in combinations(range(5),2))
    quart=sum(__import__('math').prod(signs[i] for i in I) for I in combinations(range(5),4))
    assert 1+pair+quart==16*(len(set(signs))==1)
# Exact relaxed-law obstruction: symmetric random pattern, K positives is 1/4
# with total mass 5/33 and K is 2/3 otherwise. Every four-marginal has common
# probability 1/33 but the five-event is empty. Not a cosine counterexample.
relaxed_p4=F(5,33)*F(1,5)
assert relaxed_p4==F(1,33)
print(json.dumps(dict(controls=rows,structured_count=count,structured_min=[str(best[0]),best[1]],random_count=500,random_min=[str(random_min[0]),random_min[1]],indicator_patterns=32,relaxed_p4=str(relaxed_p4),relaxed_p5='0',limits='Finite exact diagnostics, not universal proof or source refutation'),indent=2))
