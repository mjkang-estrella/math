#!/usr/bin/env python3
"""Exact finite Tate diagnostics; original code MIT, Myeongjin Kang.

No file writes, imports of local code, network, cached computations on disk,
random search, or floating-point arithmetic. All vector spaces are over Q.
"""
from fractions import Fraction as F
from itertools import product, combinations
from functools import lru_cache
import hashlib
import json


@lru_cache(None)
def mons(n, d):
    if d < 0:
        return ()
    if n == 1:
        return ((d,),)
    return tuple((a,) + b for a in range(d, -1, -1) for b in mons(n-1, d-a))


def add(a, b):
    return tuple(x+y for x, y in zip(a, b))


def rref(rows, width):
    piv = {}
    for original in rows:
        v = {i:F(c) for i,c in original.items() if c}
        while v:
            q = min(v)
            if q not in piv:
                c = v[q]
                v = {i:a/c for i,a in v.items()}
                piv[q] = v
                break
            c = v[q]
            for i,a in piv[q].items():
                v[i] = v.get(i, F(0))-c*a
                if not v[i]:
                    del v[i]
    # Back substitution gives canonical reduction modulo the relation space.
    for q in sorted(piv, reverse=True):
        for h in sorted(piv):
            if h < q and q in piv[h]:
                c = piv[h][q]
                for i,a in piv[q].items():
                    piv[h][i] = piv[h].get(i,F(0))-c*a
                    if not piv[h][i]:
                        del piv[h][i]
    return piv


class Quotient:
    def __init__(self, n, generators, top):
        self.n, self.gens, self.top = n, generators, top
        self.basis, self.relations, self.positions = {}, {}, {}
        for d in range(top+2):
            ms = mons(n,d)
            pos = {m:i for i,m in enumerate(ms)}
            rows = []
            for g in generators:
                gd = sum(next(iter(g)))
                for t in mons(n,d-gd):
                    rows.append({pos[add(m,t)]:c for m,c in g.items()})
            piv = rref(rows,len(ms))
            self.basis[d] = tuple(m for i,m in enumerate(ms) if i not in piv)
            self.relations[d] = piv
            self.positions[d] = pos
        assert not self.basis[top+1], 'quotient not zero above complete-intersection top'

    def reduce(self, g, d):
        if d < 0 or d > self.top:
            return {}
        pos, piv = self.positions[d], self.relations[d]
        v = {pos[m]:F(c) for m,c in g.items() if c}
        for q in sorted(piv):
            if q in v:
                c=v[q]
                for i,a in piv[q].items():
                    v[i]=v.get(i,F(0))-c*a
                    if not v[i]:
                        del v[i]
        ms=mons(self.n,d)
        return {ms[i]:c for i,c in v.items()}

    def mul(self, m, g):
        if not g:
            return {}
        d=sum(m)+sum(next(iter(g)))
        return self.reduce({add(m,a):c for a,c in g.items()},d)

    def hf(self):
        return tuple(len(self.basis[d]) for d in range(self.top+1))


def pure(n, degrees):
    return [{tuple(a if j==i else 0 for j in range(n)):F(1)} for i,a in enumerate(degrees)]


def lex_ideal(n, degrees, hf):
    # List all ideal monomials, not just minimal generators. Sizes are tiny.
    gs=pure(n,degrees)
    for d,h in enumerate(hf):
        box=[m for m in mons(n,d) if all(m[i]<degrees[i] for i in range(n))]
        assert 0<=h<=len(box)
        gs += [{m:F(1)} for m in box[:len(box)-h]]
    q=Quotient(n,gs,sum(a-1 for a in degrees))
    assert q.hf()==hf, 'degreewise lex prescription failed ideal closure'
    return q


def gradient_parts(f):
    degree=sum(next(iter(f)))
    out=[]
    for i in range(len(next(iter(f)))):
        g={}
        for m,c in f.items():
            if m[i]:
                a=list(m);a[i]-=1
                g[tuple(a)]=F(c)*m[i]/degree
        out.append(g)
    return out


@lru_cache(None)
def labels(n, degrees, p):
    if p < 0:
        return ()
    out=[]
    for r in range(min(n,p)+1):
        if (p-r)%2:
            continue
        for mask in combinations(range(n),r):
            for b in mons(n,(p-r)//2):
                out.append((mask,b,r+sum(a*t for a,t in zip(degrees,b))))
    return tuple(out)


def complex_part(q, fs, p, j, koszul=False, wrong_sign=False):
    n=q.n;degrees=tuple(sum(next(iter(f))) for f in fs)
    def bases(t):
        return tuple((mask,b,m) for mask,b,s in labels(n,degrees,t)
                     if not koszul or not any(b)
                     for m in q.basis.get(j-s,()))
    domain, target=bases(p),bases(p-1)
    pos={x:i for i,x in enumerate(target)}
    parts=[gradient_parts(f) for f in fs]
    xs=pure(n,(1,)*n)
    cols=[]
    for mask,b,m in domain:
        col={}
        def put(ms,bs,poly,sgn):
            for mm,c in q.mul(m,poly).items():
                k=pos[(ms,bs,mm)]
                col[k]=col.get(k,F(0))+sgn*c
                if not col[k]:
                    del col[k]
        for k,i in enumerate(mask):
            put(mask[:k]+mask[k+1:],b,xs[i],(-1)**k)
        for h,t in enumerate(b):
            if not t or koszul:
                continue
            bb=list(b);bb[h]-=1;bb=tuple(bb)
            for i,g in enumerate(parts[h]):
                if i in mask:
                    continue
                mm=tuple(sorted(mask+(i,)))
                sign=1 if wrong_sign else (-1)**sum(x<i for x in mask)
                put(mm,bb,g,sign)
        cols.append(col)
    return domain,target,cols


def compose_zero(left, right):
    # left and right are consecutive column lists.
    for col in right:
        v={}
        for k,c in col.items():
            for h,a in left[k].items():
                v[h]=v.get(h,F(0))+c*a
                if not v[h]:
                    del v[h]
        if v:
            return False
    return True


def betti(q,fs,maxp,koszul=False):
    degrees=tuple(sum(next(iter(f))) for f in fs)
    ans={}; compositions=0
    maxj=q.top+max(s for p in range(maxp+2) for _,_,s in labels(q.n,degrees,p))
    for j in range(maxj+1):
        mats=[];ranks=[];dims=[]
        for p in range(maxp+2):
            dom,tar,cols=complex_part(q,fs,p,j,koszul)
            mats.append(cols);dims.append(len(dom));ranks.append(len(rref(cols,len(tar))))
            if p>=2:
                assert compose_zero(mats[p-1],mats[p]), ('d^2',p,j)
                compositions+=1
        for p in range(maxp+1):
            b=dims[p]-ranks[p]-ranks[p+1]
            assert b>=0
            if b:
                ans[(p,j)]=b
    return ans,compositions


def table(b,maxp):
    return [[p,[[j,c] for (i,j),c in sorted(b.items()) if i==p]] for p in range(maxp+1)]


def run():
    examples=[]
    # Nonmonomial CI, with no restriction of C to a special source class.
    families=[
        ('binary-quad-cubic-powers',2,[{(2,0):1},{(0,3):1}]),
        ('binary-quad-cubic-mixed',2,[{(1,1):1},{(3,0):1,(0,3):1}]),
        ('ternary-no-square-quadrics',3,[{(2,0,0):1,(0,1,1):1},
                                        {(0,2,0):1,(1,0,1):1},
                                        {(0,0,2):1,(1,1,0):1}]),
        ('binary-cubics',2,[{(3,0):1,(1,2):1},{(0,3):1,(2,1):2}]),
    ]
    checks=0; comps=0
    for name,n,fs in families:
        degrees=tuple(sum(next(iter(f))) for f in fs);top=sum(a-1 for a in degrees)
        ring=Quotient(n,fs,top)
        expected=[1]
        for a in degrees:
            h=[0]*(len(expected)+a-1)
            for i,c in enumerate(expected):
                for t in range(a):h[i+t]+=c
            expected=h
        assert ring.hf()==tuple(expected), (name,'not certified complete-intersection HF')
        # A finite homogeneous quotient of n equations has height n in n variables,
        # so these equations form a regular sequence. No genericity assumption.
        extras=[[],[{tuple(1 if i==0 else 0 for i in range(n)):1}],
                [{tuple(1 if i==n-1 else 0 for i in range(n)):1}],
                pure(n,(1,)*n),pure(n,(2,)*n)]
        if n==3:
            extras += [[{(1,0,0):1,(0,1,0):1,(0,0,1):1}],
                       [{(2,0,0):1}], [{(1,1,0):1}],
                       [{(2,0,0):1,(0,2,0):-1}],
                       [{(2,0,0):1},{(0,2,0):1}]]
        for k,extra in enumerate(extras):
            q=Quotient(n,fs+extra,top)
            l=lex_ideal(n,degrees,q.hf())
            b,c=betti(q,fs,4);rhs,cc=betti(l,pure(n,degrees),4)
            comps+=c+cc
            bad=[(p,j,v,rhs.get((p,j),0)) for (p,j),v in b.items() if v>rhs.get((p,j),0)]
            ambient,_=betti(q,fs,n,koszul=True)
            ambient_rhs,_=betti(l,pure(n,degrees),n,koszul=True)
            assert all(v<=ambient_rhs.get(t,0) for t,v in ambient.items())
            checks+=1
            examples.append({'name':name,'extra_index':k,'degrees':degrees,'hf':q.hf(),
                             'relative':table(b,4),'lex_relative':table(rhs,4),
                             'ambient':table(ambient,n),'violations':bad})
            assert not bad, (name,k,'COUNTEREXAMPLE',bad)
        # Controls R as a free module and k with the minimal Tate ranks.
        free,_=betti(ring,fs,4)
        assert free=={(0,0):1}
        residue=Quotient(n,fs+pure(n,(1,)*n),top)
        bk,_=betti(residue,fs,4)
        expected={}
        for p in range(5):
            for _,_,j in labels(n,degrees,p):expected[(p,j)]=expected.get((p,j),0)+1
        assert bk==expected
    # Wrong wedge signs must fail d^2 on an actual quotient.
    fs=[{(2,0,0):1,(0,1,1):1},{(0,2,0):1,(1,0,1):1},
        {(0,0,2):1,(1,1,0):1}]
    q=Quotient(3,fs,3)
    rejected=False
    for j in range(4,8):
        a=complex_part(q,fs,2,j,wrong_sign=True)[2]
        b=complex_part(q,fs,3,j,wrong_sign=True)[2]
        rejected |= not compose_zero(a,b)
    assert rejected
    # Omitting the even generators wrongly computes ambient Tor: R has beta_1^S=3.
    amb,_=betti(q,fs,3,koszul=True)
    rel,_=betti(q,fs,3)
    assert amb[(1,2)]==3 and (1,2) not in rel
    # Commit the finite tables without inferring variation at a fixed ambient
    # module from comparisons involving different families.
    serial=json.dumps(examples,sort_keys=True,separators=(',',':'))
    print(json.dumps({'status':'PASS_EXACT_FINITE_DIAGNOSTICS_ONLY_C_UNRESOLVED',
                      'examples':checks,'homological_degrees':[0,4],
                      'full_internal_range_for_these_degrees':True,
                      'consecutive_differential_compositions_checked':comps,
                      'negative_controls':['wrong-wedge-sign','omit-even-generators'],
                      'data_sha256':hashlib.sha256(serial.encode()).hexdigest(),
                      'data':examples},indent=2,sort_keys=True))


if __name__=='__main__':
    run()
