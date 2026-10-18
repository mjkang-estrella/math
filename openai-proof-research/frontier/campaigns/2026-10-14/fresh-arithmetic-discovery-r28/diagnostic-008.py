#!/usr/bin/env python3
"""Finite independent checks for T008M. Original code: MIT. No proof claim."""
from collections import defaultdict
from fractions import Fraction
import json


def words(cap):
    by = [[()] if k == 0 else [] for k in range(cap+1)]
    for k in range(1, cap+1):
        by[k] = [(d,)+v for d in range(3,k+1,2) for v in by[k-d]]
    return by


def states(cap):
    m = max(1,cap//2); b = cap-m
    ws = words(cap)
    ps = [('P',a,r) for k in range(m) for a in ws[k] for r in range(1,m-k+1)]
    qs = [('Q',v,s) for k in range(b+1) for v in ws[k] for s in range(b-k+1)]
    def level(x):
        side,w,g=x
        return (-1 if side=='P' else 1)*(sum(w)+g)
    ss=sorted(ps+qs,key=lambda x:(level(x),x))
    return ss,[level(s) for s in ss]


def block(cap,mutation=None):
    ss,levels=states(cap); index={s:i for i,s in enumerate(ss)}
    mats={}
    for d in range(3,cap+3,2):
        mat={}
        for i,(side,w,g) in enumerate(ss):
            targets=[]
            if side=='P':
                if w and w[0]==d: targets.append(('P',w[1:],g))
                if not w and d>=g and mutation!='no_crossing':
                    if mutation!='unit_prefix_gap' or g==1: targets.append(('Q',(),d-g))
            else:
                v=(d,)+w if mutation=='prepend_suffix' else w+(d,)
                targets.append(('Q',v,g))
            for t in targets:
                if t in index:
                    j=index[t]
                    assert levels[j]-levels[i]==d
                    assert i<j
                    mat[i,j]=1
        mats[d]=mat
    return ss,levels,mats


def mul(a,b):
    br=defaultdict(list)
    for (j,k),v in b.items(): br[j].append((k,v))
    out=defaultdict(int)
    for (i,j),u in a.items():
        for k,v in br[j]: out[i,k]+=u*v
    return {ij:x for ij,x in out.items() if x}


def evaluation(w,ss,mats):
    out={(i,i):1 for i in range(len(ss))}
    for d in w: out=mul(out,mats.get(d,{}))
    return out


def rank(rows):
    pivots={}
    for row in rows:
        v={k:Fraction(x) for k,x in row.items() if x}
        while v:
            k=min(v)
            if k not in pivots:
                a=v[k]; pivots[k]={j:x/a for j,x in v.items()}; break
            a=v[k]
            for j,x in pivots[k].items():
                v[j]=v.get(j,0)-a*x
                if not v[j]: v.pop(j,None)
    return len(pivots)


def extraction(cap,w):
    cut=max(1,cap//2); total=0
    for i,d in enumerate(w):
        if total+d>=cut:
            a=w[:i];v=w[i+1:]
            return ('P',a,cut-total),('Q',v,cap-cut-sum(v))
        total+=d
    raise AssertionError('missing crossing')


def run():
    report={'top_checks':[],'full_rank_checks':[],'product_checks':0,'mutation_controls':{}}
    for cap in range(1,25):
        ss,levels,mats=block(cap); index={s:i for i,s in enumerate(ss)}
        ws=words(cap)
        images={w:evaluation(w,ss,mats) for w in ws[cap]}
        for w in ws[cap]:
            p,q=extraction(cap,w); entry=(index[p],index[q])
            for v in ws[cap]: assert images[v].get(entry,0)==int(v==w)
        # State counting is checked against the independent word recurrence.
        a=[1,0,0]+[0]*max(0,cap-2)
        for k in range(3,cap+1): a[k]=a[k-2]+a[k-3]
        assert [len(x) for x in ws]==a[:cap+1]
        m=max(1,cap//2);b=cap-m
        expected=sum((m-j)*a[j] for j in range(m))+sum((b-j+1)*a[j] for j in range(b+1))
        assert len(ss)==expected
        # Exhaust all words of weights cap+1,...,cap+6 for cutoff tests.
        for bucket in words(cap+6)[cap+1:]:
            for w in bucket: assert not evaluation(w,ss,mats)
        report['top_checks'].append({'cap':cap,'dimension':len(ss),'top_words':len(ws[cap])})
    for n in range(3,19):
        blocks=[block(t) for t in range(n-2,n+1)]
        allwords=[w for bucket in words(n) for w in bucket]
        rows=[]
        for w in allwords:
            row={}
            for bi,(ss,levels,mats) in enumerate(blocks):
                for (i,j),a in evaluation(w,ss,mats).items():
                    assert levels[j]-levels[i]==sum(w)
                    row[bi,i,j]=a
            rows.append(row)
        exactrank=rank(rows)
        assert exactrank==len(allwords)
        report['full_rank_checks'].append({'N':n,'algebra_dimension':len(allwords),'exact_rational_rank':exactrank})
    # Multiplication against independently concatenated free words, including cutoff.
    for n in range(3,13):
        ss,levels,mats=block(n)
        ws=[w for bucket in words(n) for w in bucket]
        ims={w:evaluation(w,ss,mats) for w in ws}
        for u in ws:
            for v in ws:
                wanted=ims[u+v] if sum(u)+sum(v)<=n else {}
                assert mul(ims[u],ims[v])==wanted
                report['product_checks']+=1
    # Broken construction controls must fail exact coefficient extraction.
    for name,cap,w in [('no_crossing',9,(9,)),('unit_prefix_gap',9,(9,)),('prepend_suffix',19,(3,3,3,5,5))]:
        ss,_,mats=block(cap,name); idx={s:i for i,s in enumerate(ss)}
        # For the reversal control use a suffix with distinct letters.
        if name=='prepend_suffix': cap=19;w=(3,3,5,3,5)
        p,q=extraction(cap,w)
        actual=evaluation(w,ss,mats).get((idx[p],idx[q]),0)
        assert actual!=1,(name,actual)
        report['mutation_controls'][name]={'cap':cap,'word':w,'entry':actual,'expected':1,'detected':True}
    # Independent weighted Lyndon-word counts versus logarithmic Mobius formula.
    def mobius(n):
        primes=0;p=2
        while p*p<=n:
            if n%p==0:
                n//=p;primes+=1
                if n%p==0:return 0
                while n%p==0:n//=p
            p+=1
        if n>1:primes+=1
        return (-1)**primes
    traces=[3,0,2]
    for n in range(3,25):traces.append(traces[n-2]+traces[n-3])
    q=[0]+[traces[n]-1-(-1)**n for n in range(1,25)]
    report['witt_checks']=[]
    for n,bucket in enumerate(words(24)):
        if not n:continue
        lyndon=sum(bool(w) and all(w<w[i:]+w[:i] for i in range(1,len(w))) for w in bucket)
        numerator=sum(mobius(d)*q[n//d] for d in range(1,n+1) if n%d==0)
        assert numerator==n*lyndon
        report['witt_checks'].append({'weight':n,'Lyndon_words':lyndon,'Witt_numerator':numerator})
    report['status']='PASS_FINITE_DIAGNOSTIC_NOT_PROOF' 
    print(json.dumps(report,indent=2))

if __name__=='__main__': run()
