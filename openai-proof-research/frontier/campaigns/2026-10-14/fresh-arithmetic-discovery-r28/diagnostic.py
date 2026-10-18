#!/usr/bin/env python3
"""Finite monomial screen; modular search, exact rational witness verification.
Not a proof of a universal rigidity assertion. Original code: MIT.
"""
from functools import lru_cache
from itertools import combinations
import json

@lru_cache(None)
def downsets(n):
    if n == 0: return (0,1)
    old=downsets(n-1); shift=1<<(n-1)
    return tuple(a | (b<<shift) for a in old for b in old if b & ~a == 0)

def rank_mod(rows, p=1000003):
    if not rows:return 0
    a=[r[:] for r in rows]; m=len(a); n=len(a[0]); r=0
    for c in range(n):
        pivot=next((i for i in range(r,m) if a[i][c]%p),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r]; inv=pow(a[r][c],-1,p)
        a[r]=[(x*inv)%p for x in a[r]]
        for i in range(r+1,m):
            z=a[i][c]%p
            if z:a[i]=[(x-z*y)%p for x,y in zip(a[i],a[r])]
        r+=1
        if r==m:break
    return r

def rank_rational(rows):
    from fractions import Fraction
    if not rows:return 0
    a=[[Fraction(x) for x in row] for row in rows]; m=len(a); n=len(a[0]); r=0
    for c in range(n):
        pivot=next((i for i in range(r,m) if a[i][c]),None)
        if pivot is None:continue
        a[r],a[pivot]=a[pivot],a[r]; z=a[r][c]
        a[r]=[x/z for x in a[r]]
        for i in range(r+1,m):
            z=a[i][c]
            if z:a[i]=[x-z*y for x,y in zip(a[i],a[r])]
        r+=1
        if r==m:break
    return r

@lru_cache(None)
def homology(n, family, exact=False):
    levels=[[s for s in range(1<<n) if family>>s&1 and s.bit_count()==r] for r in range(n+1)]
    ranks=[0]
    for r in range(n):
        rows=[]
        for t in levels[r+1]:
            row=[]
            for s in levels[r]:
                v=t^s
                if s&t==s and v.bit_count()==1:
                    row.append((-1)**((t&(v-1)).bit_count()))
                else:row.append(0)
            rows.append(row)
        if exact:
            ranks.append(rank_rational(rows))
        else:ranks.append(rank_mod(rows))
    ranks.append(0)
    return tuple(len(levels[r])-ranks[r]-ranks[r+1] for r in range(n+1))

def betti(n,family,exact=False):
    out={}; full=(1<<n)-1
    for b in range(1<<n):
        if not family>>b&1:continue
        remaining=full^b; a=remaining
        while True:
            vertices=[i for i in range(n) if a>>i&1]; k=len(vertices); link=0
            for c in range(1<<k):
                oldc=sum(1<<vertices[i] for i in range(k) if c>>i&1)
                if family>>(b|oldc)&1:link|=1<<c
            for r,h in enumerate(homology(k,link,exact)):
                if h:
                    key=(b.bit_count()+k-r,2*b.bit_count()+k)
                    out[key]=out.get(key,0)+h
            if not a:break
            a=(a-1)&remaining
    return out

def total(n,bet):return [sum(v for (p,j),v in bet.items() if p==i) for i in range(n+1)]
def hf(n,fam):return [sum(1 for s in range(1<<n) if fam>>s&1 and s.bit_count()==r) for r in range(n+1)]
def lex(n,fam):
    h=hf(n,fam); ans=0
    for r in range(n+1):
        mons=sorted((s for s in range(1<<n) if s.bit_count()==r),key=lambda s:tuple((s>>i)&1 for i in range(n)))
        for s in mons[:h[r]]:ans|=1<<s
    assert ans in downsets(n)
    return ans

def generators(n,fam):
    result=[]
    for i in range(n):
        if fam>>(1<<i)&1:result.append([2 if j==i else 0 for j in range(n)])
    for s in range(1,1<<n):
        if fam>>s&1:continue
        if all(fam>>(s^(1<<i))&1 for i in range(n) if s>>i&1):result.append([(s>>i)&1 for i in range(n)])
    return result

def main():
    counts=[]
    for n in range(1,6):
        checked=0; cache={}
        for fam in downsets(n):
            if not fam&1:continue
            if not all(fam>>(1<<i)&1 for i in range(n)):continue
            jfam=lex(n,fam)
            if jfam not in cache:cache[jfam]=betti(n,jfam)
            a=betti(n,fam); b=cache[jfam]; aa=total(n,a); bb=total(n,b)
            assert all(a.get(k,0)<=v for k,v in b.items()) and all(k in b for k in a)
            checked+=1
            for i in range(1,n):
                if aa[i]==bb[i] and aa[i+1:]!=bb[i+1:]:
                    assert a==betti(n,fam,True) and b==betti(n,jfam,True)
                    result={'status':'COUNTEREXAMPLE','n':n,'equality_index':i,'standard_face_mask':fam,'lex_face_mask':jfam,'hilbert_function':hf(n,fam),'I_generators':generators(n,fam),'J_generators':generators(n,jfam),'I_total':aa,'J_total':bb,'I_graded':[[p,j,v] for (p,j),v in sorted(a.items())],'J_graded':[[p,j,v] for (p,j),v in sorted(b.items())],'earlier_counts':counts,'current_checked':checked,'verification':'full Koszul multidegrees; exact rational ranks for witness'}
                    print(json.dumps(result,indent=2));return
        counts.append({'n':n,'checked':checked})
        print(json.dumps(counts[-1]),flush=True)
    print(json.dumps({'status':'NO_COUNTEREXAMPLE_IN_FINITE_SCREEN','counts':counts}))
if __name__=='__main__':main()
