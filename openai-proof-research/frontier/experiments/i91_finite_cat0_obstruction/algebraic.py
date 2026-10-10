"""Bounded, exact rational interval search on the actual Fano configuration.

This is NOT a CAT(0) realization test. No contradiction means inconclusive.
The zero-error radial and CD identities are paid by the report's limits.
All intervals are dyadic integers; division rounds outwards. No writes.
"""
import json
from itertools import combinations
from fractions import Fraction as F
from template import template, line

def run(include_trace=False):
    t=template(); names=t['vertices']+['c','JA','JB','JC','JD']
    mids=[]
    for opp in t['opposites']:
        for a,b in sorted(opp):mids.append(('c',a,b))
    for label,i in zip('ABCD',(1,2,4,7)):
        j='J'+label;mids.append((j,'X'+str(i),'Y'+str(i)))
        full=sorted(t['adj']['Y'+str(i)])
        for a,b in combinations(full,2):mids.append((j,a,b))
    mids.append(('c','JC','JD'))
    for n,a,b in [('u',line(1,4),'JD'),('up',line(2,4),'JD'),('v',line(1,7),'JC'),('vp',line(2,7),'JC'),('m','u','v'),('mp','up','vp')]:
        names.append(n);mids.append((n,a,b))
    names=sorted(names);mids=sorted(set(mids));pairs=list(combinations(names,2)); ix={p:i for i,p in enumerate(pairs)}
    def key(a,b):return ix[tuple(sorted((a,b)))] if a!=b else None
    scale=1<<24;lo=[0]*len(pairs);hi=[4*scale]*len(pairs)
    def fix(a,b,q):
        k=key(a,b);q=F(q)*scale;assert q.denominator==1
        if k is not None:lo[k]=max(lo[k],int(q));hi[k]=min(hi[k],int(q));assert lo[k]<=hi[k]
    for a,b in t['edges']:fix(a,b,1)
    for v in t['vertices']:
        fix('c',v,F(3,4))
        for a,b in combinations(sorted(t['adj'][v]),2):fix(a,b,2)
    for opp in t['opposites']:
        for a,b in opp:fix(a,b,3)
    for j in ('JA','JB','JC','JD'):fix('c',j,F(1,4))
    fix('JC','JD',1);fix('JC','X7',F(3,2))
    rows=set()
    def add(terms):
        row={}
        for coeff,a,b in terms:
            k=key(a,b)
            if k is not None:row[k]=row.get(k,0)+F(coeff)
        row={k:c for k,c in row.items() if c}
        if not row:return
        from math import lcm,gcd
        mul=lcm(*(x.denominator for x in row.values()))
        ints={k:int(c*mul) for k,c in row.items()};g=gcd(*ints.values())
        rows.add(tuple(sorted((k,c//g) for k,c in ints.items())))
    for m,a,b in mids:
        # Endpoint identities and midpoint convexity at every named point.
        for z in (a,b):
            add([(4,m,z),(-1,a,b)]);add([(-4,m,z),(1,a,b)])
        for z in names:add([(4,m,z),(-2,a,z),(-2,b,z),(1,a,b)])
    for a,b,c,d in combinations(names,4):
        for u,v,w,z in [(a,b,c,d),(a,c,b,d),(a,d,b,c)]:
            add([(1,u,v),(1,w,z),(-1,u,w),(-1,w,v),(-1,v,z),(-1,z,u)])
    # Selected Young-Reshetnyak rows: one arrow connects c to a named point.
    for z in names:
        if z=='c':continue
        for a,b in pairs:
            if len({'c',z,a,b})<4:continue
            for q in (F(2,5),F(1,2),F(1),F(2),F(5,2)):
                for sign in (-1,1):
                    add([(sign,'c',b),(sign,z,a),(-sign,'c',a),(-sign,z,b),(-q,'c',z),(-1/q,a,b)])
    rows=sorted(rows);rounds=[];contradiction=None;trace=[]
    initial=list(zip(lo,hi))
    # At most 8 full sweeps; this is intentionally a bounded diagnostic.
    for sweep in range(8):
        changes=0
        for ri,row in enumerate(rows):
            minsum=sum(co*(lo[k] if co>0 else hi[k]) for k,co in row)
            if minsum>0:contradiction={'row':ri,'positive_minimum':minsum,'sweep':sweep};break
            for k,co in row:
                rest=minsum-co*(lo[k] if co>0 else hi[k])
                if co>0:
                    upper= -(rest//co) # ceil(-rest/co): round OUTWARDS
                    if upper<hi[k]:
                        hi[k]=upper;changes+=1;trace.append([ri,k,'upper',upper])
                else:
                    lower=rest//(-co) # floor(rest/(-co)): round OUTWARDS
                    if lower>lo[k]:
                        lo[k]=lower;changes+=1;trace.append([ri,k,'lower',lower])
                if lo[k]>hi[k]:contradiction={'variable':list(pairs[k]),'sweep':sweep};break
            if contradiction:break
        rounds.append(changes)
        if contradiction or not changes:break
    chosen=[('JA','JB'),('u','up'),('v','vp'),('u','v'),('u','vp'),('m','mp'),('c','m')]
    result={'status':'CONTRADICTION_REQUIRES_TRACE_REVIEW' if contradiction else 'INCONCLUSIVE_NO_CERTIFICATE', 'points':len(names),'variables':len(pairs),'midpoint_identities':len(mids),'inequalities':len(rows),'dyadic_denominator':scale,'sweeps':rounds,'updates':len(trace),'max_row_l1':max(sum(abs(c) for k,c in row) for row in rows),'contradiction':contradiction,'intervals':{'|'.join(p):[str(F(lo[key(*p)],scale)),str(F(hi[key(*p)],scale))] for p in chosen}}
    if include_trace:result.update(names=names,pairs=pairs,midpoints=mids,initial=initial,rows=rows,trace=trace)
    return result

if __name__=='__main__':print(json.dumps(run(),sort_keys=True,indent=2))
