#!/usr/bin/env python3
"""Finite exact supporting checks, not proofs of an asymptotic Liouville claim."""
from collections import Counter,defaultdict
from fractions import Fraction
from itertools import product,combinations
from pathlib import Path
import json,math
ROOT=Path(__file__).resolve().parent

def prod(xs):return math.prod(xs)
def model(r,sigma,mutate=False):
    L=2*r+1
    out=[]
    for phase in range(r):
        # For n=0,...,2r-1, at most three separator labels are encountered.
        for bits in product((-1,1),repeat=(r-1)+3+1):
            A=bits[:r-1];C=bits[r-1:r+2];z=bits[-1];x=[z]
            for n in range(L-1):
                k,j=divmod(n+phase,r)
                d=(sigma**k)*A[j] if j<r-1 else (1 if mutate else C[k])
                x.append(x[-1]*d)
            out.append(tuple(x))
    return out

def moments(samples):
    L=len(samples[0]);N=len(samples)
    singles=[sum(x[i] for x in samples) for i in range(L)]
    pairs={(i,j):sum(x[i]*x[j] for x in samples) for i,j in combinations(range(L),2)}
    return singles,pairs

answer={'scope':'Exact finite supporting checks only; no new Liouville theorem or novelty certification.'}
# Pointwise telescoping plus the sign inequality giving the sharp bound.
pointwise=0
for r in range(2,7):
    for x in product((-1,1),repeat=2*r+1):
        Y=[x[j]*x[j+1]*x[j+r]*x[j+r+1] for j in range(r)]
        assert prod(Y)==x[0]*x[2*r]
        for s in (-1,1):assert s*sum(Y)<=r-1+(s**r)*prod(Y)
        pointwise+=1
answer['pointwise_configurations']=pointwise
results=[]
for r in range(2,9):
    for sigma in (-1,1):
        samples=model(r,sigma);N=len(samples)
        one,two=moments(samples)
        assert all(t==0 for t in one) and all(t==0 for t in two.values())
        c=Fraction(sum(x[0]*x[1]*x[r]*x[r+1] for x in samples),N)
        assert c==sigma*Fraction(r-1,r)
        for mask in range(1,32):
            if mask.bit_count()%2:assert sum(prod(x[j] for j in range(5) if mask>>j&1) for x in samples)==0
        results.append({'r':r,'sigma':sigma,'samples':N,'four_point':str(c)})
answer['sharp_models']=results
# A simpler equivalent r=2 model, enabling exact five-word probabilities.
words=Counter()
for R,B,U0,U1,U2 in product((-1,1),repeat=5):
    U=(U0,U1,U2);phase=(R+1)//2
    w=tuple(U[(n+phase)//2]*(B if (n+phase)%2 else 1) for n in range(5))
    words[w]+=1
allwords=list(product((-1,1),repeat=5))
for w in allwords:
    p=Fraction(words[w],32)
    q=Fraction(1,32)*(1+Fraction(prod(w[:4]),2)+Fraction(prod(w[1:]),2))
    assert p==q
assert sum(v>0 for v in words.values())==24
answer['five_word_model']={'positive_patterns':24,'zero_patterns':[''.join('+' if t==1 else '-' for t in w) for w in allwords if not words[w]],'probability_histogram':{str(k):v for k,v in Counter(Fraction(words[w],32) for w in allwords).items()}}
# Deliberate mutation: losing fresh separators destroys pairwise independence.
bad=model(3,1,True);one,two=moments(bad)
assert any(v!=0 for v in two.values())
answer['mutation_rejected']=True
# Exact host-minus-matching switch obstruction on six vertices.
n=6;forbidden={(0,1),(2,3),(4,5)};E=[e for e in combinations(range(n),2) if e not in forbidden]
ix={e:i for i,e in enumerate(E)};target=(3,1,3,1,3,1);states=[]
for mask in range(1<<len(E)):
    d=[0]*n
    for i,(a,b) in enumerate(E):
        if mask>>i&1:d[a]+=1;d[b]+=1
    if tuple(d)==target:states.append(mask)
assert len(states)==2
state_edges=[{e for i,e in enumerate(E) if mask>>i&1} for mask in states]
assert len(state_edges[0]^state_edges[1])==6 # A four-edge switch cannot connect.
for F in state_edges:
    for e,f in combinations(F,2):
        a,b=e;c,d=f
        if len({a,b,c,d})<4:continue
        for q,t in [((a,c),(b,d)),((a,d),(b,c))]:
            q=tuple(sorted(q));t=tuple(sorted(t))
            assert not(q in ix and t in ix and q not in F and t not in F)
answer['host_obstruction']={'n':n,'forbidden':sorted(forbidden),'degrees':target,'two_states':[sorted(F) for F in state_edges],'switch_neighbors':0}
(ROOT/'exact-results.json').write_text(json.dumps(answer,indent=2)+'\n')
print(json.dumps(answer,indent=2))
