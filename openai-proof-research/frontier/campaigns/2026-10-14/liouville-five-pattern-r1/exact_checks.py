#!/usr/bin/env python3
"""Exact rational checks for the Sawin-type degree-one model, not for D1.

The (alpha,beta) square [0,2)^2 is partitioned by beta+j*alpha=k.
In each open alpha stripe all boundary lines have fixed order. Cell widths
are affine, so their integrals equal stripe width times midpoint width.
This is exact polygon integration, not sampling or a numerical simulation.
"""
from fractions import Fraction as Q
from itertools import product, combinations
from collections import defaultdict, Counter
from pathlib import Path
import json

def sign(t):
    return 1 if (t.numerator // t.denominator) % 2 == 0 else -1

def wordstr(w):
    return ''.join('+' if s == 1 else '-' for s in w)

def law(m):
    crit = sorted({Q(0), Q(2)} | {Q(k,d) for d in range(1,m)
                   for k in range(2*d+1)})
    probs = defaultdict(Q)
    stripes=[]
    for l,r in zip(crit,crit[1:]):
        a=(l+r)/2
        bs=sorted({Q(0),Q(2)} | {Q(k)-j*a for j in range(m)
                       for k in range(2*m+1) if 0 < Q(k)-j*a < 2})
        cond=defaultdict(Q)
        for u,v in zip(bs,bs[1:]):
            b=(u+v)/2
            w=tuple(sign(b+j*a) for j in range(m))
            cond[w]+=(v-u)/2
            probs[w]+=(r-l)*(v-u)/4
        assert sum(cond.values())==1
        moment=lambda inds:sum(p*prod(w[i] for i in inds) for w,p in cond.items())
        row={'left':str(l),'right':str(r)}
        if m==5:
            row.update(a=str(moment([0,1,2,3])),b=str(moment([0,1,2,4])),
                       c=str(moment([0,1,3,4])))
        stripes.append(row)
    for w in product([-1,1],repeat=m):
        probs[w]+=0
    assert sum(probs.values())==1
    return probs,stripes

def prod(xs):
    p=1
    for x in xs:p*=x
    return p

p,rows=law(5)
moment=lambda inds:sum(pr*prod(w[i] for i in inds) for w,pr in p.items())
a,b,c=(moment(I) for I in ([0,1,2,3],[0,1,2,4],[0,1,3,4]))
assert (a,b,c)==(Q(1,3),Q(0),Q(1,3))
assert all(moment(I)==0 for k in (1,2,3,5) for I in combinations(range(5),k))
coeffs=defaultdict(list)
for w,pr in sorted(p.items()):
    P=prod(w)
    coeff=(P*(w[0]+w[4]),P*(w[1]+w[3]),P*w[2])
    coeffs[coeff].append(wordstr(w))
    assert 32*pr == 1+coeff[0]*a+coeff[1]*b+coeff[2]*c
    assert pr==p[tuple(-s for s in w)]==p[w[::-1]]
expected={(0,0,1)}|{(s*2,t*2,1) for s,t in product([-1,1],repeat=2)}|{
    (s*2,0,-1) for s in [-1,1]}|{(0,s*2,-1) for s in [-1,1]}
assert set(coeffs)==expected
missing=[wordstr(w) for w,pr in sorted(p.items()) if not pr]
assert missing==['---+-','-+---','+-+++','+++-+']
p4,_=law(4)
assert len([x for x in p4.values() if x])==16
res={
    'status':'exact support/model checks only; original Liouville D1 remains unresolved',
    'integration':'rational affine-cell integration on [0,2)^2; no Monte Carlo',
    'moments':{'a':str(a),'b':str(b),'c':str(c)},
    'five_word_probabilities':{wordstr(w):str(pr) for w,pr in sorted(p.items())},
    'probability_histogram':{str(pr):n for pr,n in sorted(Counter(p.values()).items())},
    'missing_words':missing,
    'four_word_support':16,
    'four_word_minimum':str(min(p4.values())),
    'coefficient_classes':[{ 'coefficient':list(q),'words':v } for q,v in sorted(coeffs.items())],
    'alpha_stripes_and_conditional_four_moments':rows,
    'exact_assertions':['total mass one','all one-, two-, three-, five-moments zero',
       'global sign and reversal invariance','TT Eq 7.4 on all 32 words',
       'all coefficient classes enumerated','missing four words','all length-four words positive']
}
out=Path(__file__).with_name('exact-results.json')
out.write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps({k:res[k] for k in ('status','moments','probability_histogram','missing_words','four_word_minimum')},indent=2))
