#!/usr/bin/env python3
"""Exact exploratory checks on finite positive-tree posterior laws; not a proof."""
from fractions import Fraction as Q
from itertools import permutations, combinations_with_replacement
from pathlib import Path
import json

THIRD=Q(1,3)
def validate(a):
    assert sum(a.values())==1
    assert all(w>0 and sum(p)==1 and min(p)>=0 for p,w in a.items())
    assert all(sum(w*p[i] for p,w in a.items())==THIRD for i in range(3))
    for p,w in a.items():
        assert all(a[t]==w for t in set(permutations(p)))
    return a

def orbit(p):
    atoms=set(permutations(p));return validate({t:Q(1,len(atoms)) for t in atoms})

def channel(a,t):
    b={}
    for p,w in a.items():
        z=tuple(THIRD+t*(x-THIRD) for x in p)
        b[z]=b.get(z,Q(0))+w
    return validate(b)

def product(a,b):
    out={}
    for p,x in a.items():
        for q,y in b.items():
            v=tuple(p[i]*q[i] for i in range(3));s=sum(v)
            if s==0:continue
            z=tuple(t/s for t in v)
            out[z]=out.get(z,Q(0))+3*s*x*y
    return validate(out)

def info(a):
    return sum(w*(3*sum(x*x for x in p)-1)/2 for p,w in a.items())

def product_info(a,b):
    # Direct marginal-tilt expectation, independent of normalized-output grouping.
    ans=Q(0)
    for p,x in a.items():
        for q,y in b.items():
            v=tuple(p[i]*q[i] for i in range(3));s=sum(v)
            if s:ans+=x*y*Q(3,2)*(3*sum(t*t for t in v)/s-s)
    return ans

R=orbit((Q(1),Q(0),Q(0)));U=orbit((THIRD,THIRD,THIRD))
negative=orbit((Q(0),Q(1,2),Q(1,2)))
assert info(negative)==Q(1,4) and product_info(negative,negative)==Q(5,8)
assert info(product(negative,negative))==Q(5,8)
pool={}; trees={}
def add(name,law,tree):pool[name]=law;trees[name]=tree
for t in [Q(1,10),Q(1,4),Q(1,2),Q(4,5),Q(1)]:
    name=f'edge({t})';add(name,channel(R,t),{'edge':str(t),'child':'revealing leaf'})
for t in [Q(1,4),Q(1,2),Q(4,5)]:
    a=channel(R,t)
    for degree in range(2,5):
        a=product(a,channel(R,t));name=f'star({degree},{t})'
        add(name,a,{'children':[{'edge':str(t),'child':'revealing leaf'}]*degree})
        if degree==2:
            expected=t*t/Q(3)*((2+t)**2/(1+2*t*t)+2*(1-t)/(1+t))
            assert info(a)==expected
for t in [Q(1,4),Q(1,2),Q(4,5)]:
    name=f'branch(1/2,star(2,{t}))';add(name,channel(pool[f'star(2,{t})'],Q(1,2)),{'edge':'1/2','child':trees[f'star(2,{t})']})
a=product(pool['branch(1/2,star(2,1/4))'],pool['branch(1/2,star(2,4/5))'])
add('mixed-depth2',a,{'children':[trees['branch(1/2,star(2,1/4))'],trees['branch(1/2,star(2,4/5))']]})
# Exactly enumerate pairs of these specified trees. No sampling or rounding.
rows=[]
for na,nb in combinations_with_replacement(pool,2):
    a,b=pool[na],pool[nb];x,y=info(a),info(b);z=product_info(a,b)
    ratio=(x+y-z)/(x*y)
    rows.append({'left':na,'right':nb,'a':str(x),'b':str(y),'product':str(z),'saving_ratio':str(ratio),'c1_holds':ratio>=1})
minimum=min(rows,key=lambda r:Q(r['saving_ratio']))
result={'status':'EXPLORATORY EXACT FINITE CHECKS ONLY','laws':len(pool),'pairs':len(rows),'minimum':minimum,'c1_violations':[r for r in rows if not r['c1_holds']], 'controls':['exclusion law correctly violates subadditivity','two-branch equal-channel formula','exact normalization, positivity, balance and permutation symmetry of every constructed law'], 'trees':{name:{'tree':trees[name],'atoms':len(law),'information':str(info(law))} for name,law in pool.items()},'results':rows,'limitations':'No universal inequality, class preservation theorem, capacity necessity or new-result acceptance follows.'}
p=Path(__file__).resolve().parent
(p/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({key:result[key] for key in ['status','laws','pairs','minimum','c1_violations']},indent=2))
