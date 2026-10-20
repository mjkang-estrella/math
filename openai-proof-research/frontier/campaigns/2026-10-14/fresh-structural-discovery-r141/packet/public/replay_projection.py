#!/usr/bin/env python3
"""Bounded exact arithmetic check of the prefreeze representation, not a proof.
Reads/writes no files. Standard library only. Emits a JSON receipt to stdout.
"""
import itertools, json, datetime

def coverage(blocks):
    return lambda mask: sum(w for block,w in blocks if mask & block)

def run(n, blocks1, blocks2):
    r1,r2=coverage(blocks1),coverage(blocks2)
    E=(1<<n)-1; R=r1(E); assert R==r2(E)
    ranks1=[r1(s) for s in range(1<<n)]
    ranks2=[r2(s) for s in range(1<<n)]
    omega=[]
    for x in itertools.product(range(R+1),repeat=n):
        if sum(x)!=R:continue
        if all(sum(x[i] for i in range(n) if s>>i&1)<=min(ranks1[s],ranks2[s]) for s in range(1<<n)):
            omega.append(x)
    # Empty instances exercise the exact zero branch; the rank construction is conditional on feasibility.
    if not omega:return {'n':n,'R':R,'empty':True,'visible_sets_checked':0}
    checked=0
    for A in range(1<<n):
        ai=[i for i in range(n) if A>>i&1]; di=[i for i in range(n) if not A>>i&1]
        W=ai+[n+i for i in ai]; J=di+[n+i for i in di]
        def lift(mask,indices):return sum(1<<i for j,i in enumerate(indices) if mask>>j&1)
        def f(mask):
            left=mask&E; right=(mask>>n)&E
            dual=R*right.bit_count()-R+r2(E^right)
            aux=R*sum(bool(mask & ((1<<i)|(1<<(n+i)))) for i in di)
            return r1(left)+dual+aux
        gs=[]
        for S in range(1<<len(W)):
            v=lift(S,W)
            gs.append(min(f(v|lift(T,J))-R*T.bit_count() for T in range(1<<len(J))))
        assert gs[0]==0 and gs[-1]==len(ai)*R
        for s in range(len(gs)):
            for t in range(len(gs)):
                assert gs[s]+gs[t]>=gs[s|t]+gs[s&t]
                if s&t==s:assert gs[s]<=gs[t]
        represented=set()
        for x in itertools.product(range(R+1),repeat=len(ai)):
            y=x+tuple(R-z for z in x)
            if all(sum(y[i] for i in range(len(W)) if s>>i&1)<=gs[s] for s in range(len(gs))):
                represented.add(x)
        expected={tuple(x[i] for i in ai) for x in omega}
        assert represented==expected,(n,R,A,represented,expected)
        checked+=1
    return {'n':n,'R':R,'empty':False,'original_vectors':len(omega),'visible_sets_checked':checked}

if __name__=='__main__':
    cases=[
      (3,[(1,1),(6,1)],[(2,1),(5,1)]), # I13 noncommuting separate projections
      (3,[(7,2)],[(3,1),(6,1)]),
      (3,[(3,2),(4,1)],[(5,1),(6,2)]),
      (3,[(1,2)],[(2,2)]), # infeasible
      (3,[(7,0)],[(7,0)]), # rank zero
      (4,[(3,1),(12,1)],[(5,1),(10,1)]),
      (4,[(15,2)],[(7,1),(14,1)]),
      (2,[(3,3)],[(1,1),(2,2)])]
    results=[run(*c) for c in cases]
    print(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'purpose':'finite arithmetic validation only; no mathematical gate','cases':results,'status':'all exact comparisons agreed'},indent=2))
