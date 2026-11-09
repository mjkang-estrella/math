"""Reviewer-written exact tests. No imports from, or writes to, candidate lane.

1. Literal edge-orientation enumeration (no sparse-polynomial multiplication).
2. Hamiltonian-path subset DP for rational divided symmetrization (no descent formula).
3. Exhaustive audit of the restricted appendix transfer conditions.
Finite tests are error detectors, not an all-n proof or novelty evidence.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product
from functools import lru_cache
from math import comb, prod
import json, time
HERE=Path(__file__).resolve().parent

def target(n,k): return (-1)**(n-1)*comb(n,k)*comb(n-2,k-1)

def literal(n,k):
    # Directly construct the translated NE_(n-1), then the two other sets.
    pieces=[{(i,j+1) for i in range(1,n) for j in range(1,n) if i<j},
            {(n,j) for j in range(1,k+1)}, {(i,1) for i in range(k+1,n)}]
    edges=sorted(set.union(*pieces))
    assert len(edges)==sum(map(len,pieces))==n*(n-1)//2
    out=0; stair=list(range(n)); vectors=0
    for bits in product((0,1),repeat=len(edges)):
        exps=[0]*n
        for b,(i,j) in zip(bits,edges):exps[(j if b else i)-1]+=1
        if sorted(exps)!=stair:continue
        vectors+=1
        inv=sum(exps[i]<exps[j] for i in range(n) for j in range(i+1,n))
        out+=(-1)**(sum(bits)+inv)
    return out,vectors

def monomial_ds(exps):
    n=len(exps); x=tuple(i*i+2*i-4 for i in range(n))
    @lru_cache(None)
    def step(mask,last):
        pos=mask.bit_count()
        if pos==n:return Q(1)
        return sum((Q(x[v]**exps[pos], x[last]-x[v])*step(mask|(1<<v),v)
                    for v in range(n) if not mask>>v&1),Q(0))
    return sum((x[v]**exps[0]*step(1<<v,v) for v in range(n)),Q(0))

def product_ds(n,k):
    # Fix first/last node, then sum over internal path order by subset DP.
    # P=(last-first) * product_(positions 2..k)(last-node)
    #                 * product_(positions k+1..n-1)(node-first).
    x=tuple(i*i+3*i-5 for i in range(n)); ans=Q(0)
    for a in range(n):
        for b in range(n):
            if a==b:continue
            interior=tuple(v for v in range(n) if v not in (a,b)); m=n-2
            @lru_cache(None)
            def dp(mask,last):
                if mask==(1<<m)-1:return Q(1,x[last]-x[b])
                position=mask.bit_count()+2
                s=Q(0)
                for vindex,v in enumerate(interior):
                    if mask>>vindex&1:continue
                    num=x[b]-x[v] if position<=k else x[v]-x[a]
                    s+=Q(num,x[last]-x[v])*dp(mask|(1<<vindex),v)
                return s
            ans+=(x[b]-x[a])*dp(0,a)
    return ans

def audit_transfer(a):
    n=len(a); pref=0;r=n-1
    for j in range(n-1):
        pref+=a[j]
        if pref<j+1:r=j;break
    old=tuple(a);a=list(a);moves=0
    for i in range(r):
        assert a[i]>=1
        while a[i]>1:
            # Remove one unit at i before forming (x_i-x_(i+1))*x^b.
            assert sum(a[:i+1])-1>=i+1
            a[i]-=1;a[i+1]+=1;moves+=1
    assert a[r]==0
    for i in range(n-1,r,-1):
        assert a[i]>=1
        while a[i]>1:
            # Reverse move crosses cut j=i in one-based notation.
            assert sum(a[:i])<=i-2
            a[i]-=1;a[i-1]+=1;moves+=1
    assert a==[int(i!=r) for i in range(n)]
    val=(-1)**(n-r-1)*comb(n-1,r)
    if n<=6:assert monomial_ds(old)==val,(old,val,monomial_ds(old))
    return moves

def main():
    t=time.time();out={'literal':[],'path_dp':[],'restricted':[],'split_checks':[]}
    for n in range(2,7):
        for k in range(1,n):
            a,c=literal(n,k);assert a==target(n,k)
            out['literal'].append({'n':n,'k':k,'value':a,'surviving_orientations':c})
        print('literal',n,flush=True)
    for n in range(2,10):
        for k in range(1,n):
            a=product_ds(n,k);assert a==target(n,k),(n,k,a)
            out['path_dp'].append({'n':n,'k':k,'value':str(a)})
        print('path_dp',n,flush=True)
    for n in range(2,11):
        count=moves=0
        for middle in product((0,1),repeat=n-2):
            leftover=n-1-sum(middle)
            for first in range(leftover+1):
                a=(first,*middle,leftover-first);moves+=audit_transfer(a);count+=1
        out['restricted'].append({'n':n,'vectors':count,'moves':moves,'numeric_dp':n<=6})
        print('restricted',n,count,flush=True)
    # All split cuts with monomial mass concentrated at arbitrary nodes.
    for n in range(2,7):
        count=0
        for j in range(1,n):
            for massleft in range(n-1):
                b=[0]*n;b[0]=massleft;b[-1]=n-2-massleft
                c=b.copy();c[j-1]+=1;d=b.copy();d[j]+=1
                actual=monomial_ds(tuple(c))-monomial_ds(tuple(d))
                expected=comb(n,j)*monomial_ds(tuple(b[:j]))*monomial_ds(tuple(b[j:])) if massleft==j-1 else 0
                assert actual==expected,(n,j,b,actual,expected);count+=1
        out['split_checks'].append({'n':n,'cases':count})
    out['negative_controls']={'n2_value':literal(2,1)[0],
        'n4k2_value':literal(4,2)[0],
        'wrong_sign_detected':literal(2,1)[0]!=2,
        'wrong_factorial_detected':literal(4,2)[0]!=24*target(4,2)}
    out['elapsed_seconds']=time.time()-t;out['status']='PASS (finite checks only)'
    (HERE/'independent-check-results.json').write_text(json.dumps(out,indent=2)+'\n')
    print(out['status'],out['elapsed_seconds'],flush=True)
if __name__=='__main__':main()
