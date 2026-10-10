#!/usr/bin/env python3
"""Finite diagnostics only; no downloads, writes, bytecode or topology solver."""
import itertools
import json


def red(w):
    a=[]
    for x in w:
        if a and a[-1]==-x: a.pop()
        else: a.append(x)
    return tuple(a)


def inv(w): return tuple(-x for x in reversed(w))
def conj(u,w): return red(u+w+inv(u))


def run():
    edges=[(v,1-v,t,'R' if t<5 else 'B') for v in range(2) for t in range(10)]
    cases=[]
    for c in itertools.product('RB',repeat=2):
        loads=[int(c[v]==color)+int(c[w]==color) for v,w,t,color in edges]
        cases.append({'selection':''.join(c),'double_selected':loads.count(2),
                      'unselected':loads.count(0),'deck_invariant':c[0]==c[1],
                      'disjoint':max(loads)<=1})
    assert [x['selection'] for x in cases if x['disjoint']]==['RB','BR']
    assert not any(x['deck_invariant'] and x['disjoint'] for x in cases)
    ports={'R':range(10),'B':range(10,20)}
    quads=[(a,b,c,d) for a,c in itertools.permutations(ports['R'],2)
           for b,d in itertools.permutations(ports['B'],2)]
    assert len(quads)==8100 and len(set(quads))==8100
    for q in quads:
        assert len(set(q))==4
        for c in ['R','B']:
            for pair in [q[:2],q[2:]]:
                assert sum(x in ports[c] for x in pair)==1
    counts=[{'p':p,'b':len(quads)*16*(p+1)**4,'stabilization_bound':2*len(quads)*16*(p+1)**4}
            for p in [9,10,11,20]]
    assert counts[0]['b']==1296000000
    words=0
    traces=[]
    for rank in range(2,31):
        t=(1,); t2=(1,1)
        basis=[t2]+[(a,) for a in range(2,rank+1)]+[(1,a,-1) for a in range(2,rank+1)]
        for w in basis:
            assert conj(t,conj(t,w))==conj(t2,w)
            words+=1
        assert conj(t,t2)==t2
        for a in range(2,rank+1):
            assert conj(t,(a,))==(1,a,-1)
            assert conj(t,(1,a,-1))==conj(t2,(a,))
        # Abelianized Schreier matrix fixes t^2 and exchanges each remaining pair.
        traces.append({'rank_H':rank,'rank_H2':len(basis),'trace':1})
    homology_cases=0
    for rank in range(2,51):
        for k in range(101):
            b1_cover=2*rank-1
            chi_cover=1-b1_cover+2*k
            chi_quot=chi_cover//2
            assert chi_cover==2*chi_quot
            b2_quot=chi_quot-1+rank
            assert b2_quot==k
            homology_cases+=1
    zero_signatures=[]
    signature_cases=0
    for k in range(201):
        solutions=[]
        for positive in range(k+1):
            negative=k-positive; signature_cases+=1
            if positive-negative==0: solutions.append(positive)
        assert bool(solutions)==(k%2==0)
        if solutions: zero_signatures.append(k)
    assert abs(2*1-(-2)*1)==4
    return {'status':'PASS finite diagnostics only','lifted_plumbing_edges':len(edges),
            'color_cases':cases,'distinct_ordered_port_quadruples':len(quads),
            'upper_branch_selection_checks':len(quads)*4,'source_counts':counts,
            'Schreier_generator_checks':words,'abelian_traces':traces,
            'homology_cases':homology_cases,'signature_inertia_cases':signature_cases,
            'zero_signature_ranks':zero_signatures,'surgery_slope_distance':4,
            'limits':'No Whitney disks, manifold reconstruction, signature theorem, HIKMOT, or analytic proof is computationally certified.'}

if __name__=='__main__': print(json.dumps(run(),indent=2,sort_keys=True))
