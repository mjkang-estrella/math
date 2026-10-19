#!/usr/bin/env python3
"""Small exact diagnostics; never a substitute for the general prose arguments."""
import itertools
import json

def rank(edges, subset, n):
    parent=list(range(n))
    def root(x):
        while parent[x]!=x:
            x=parent[x]
        return x
    value=0
    for i in subset:
        a,b=map(root,edges[i])
        if a!=b:
            parent[a]=b
            value+=1
    return value

def partitions(n):
    def extend(a):
        if len(a)==n:
            yield tuple(a)
        else:
            for j in range(max(a)+2):
                yield from extend(a+[j])
    yield from extend([0])

def density_cases(m,kappa):
    # xy; two bundles at each of v1,v2; then the bridge xu.
    edges=[(0,1)]+[(0,2)]*m+[(1,2)]*m+[(0,3)]*m+[(1,3)]*m+[(0,4)]
    flats={frozenset(i for i,(u,v) in enumerate(edges) if part[u]==part[v]) for part in partitions(5)}
    forced=set(range(1,2*m+1))
    other=list(range(2*m+1,len(edges)))
    total=0
    violations=0
    for bits in itertools.product((0,1),repeat=len(other)):
        sampled=forced|{i for i,b in zip(other,bits) if b}
        objective={f:len(f&sampled)-kappa*rank(edges,f,5) for f in flats}
        best=max(objective.values())
        violations+=any(0 not in f and val==best for f,val in objective.items())
        total+=1
    return total,violations,len(flats)

def main():
    # Flags cannot be eliminated using only affine count equalities.
    labels=['Tp','Tm','S','Z','Y','Up','Um','W','DM','DG']
    def vector(items): return tuple(int(x in items) for x in labels)
    v1=vector(['Tp','Z','Up','DM'])
    v3=vector(['S','Z','Up','DM'])
    v4=vector(['S','Y','W','DG'])
    unwanted=vector(['Tp','Y','W','DG'])
    assert tuple(a+b-c for a,b,c in zip(v4,v1,v3))==unwanted
    assert unwanted not in [v1,vector(['Tm','Z','Um','DM']),v3,v4]
    positive=density_cases(3,1)
    assert positive[1]==0
    negative=density_cases(1,2)
    assert negative[1]>0
    # Path matching rank violates the submodular-rank substitution.
    def mr(subset):
        return max(sum(bits) for bits in itertools.product((0,1),repeat=3)
                   if all(not bits[i] or i in subset for i in range(3))
                   and not(bits[0] and bits[1]) and not(bits[1] and bits[2]))
    A={0,1}; B={1,2}
    assert mr(A)+mr(B)<mr(A|B)+mr(A&B)
    # Alternating closures along an even path propagate from one end.
    for s in range(1,21):
        current={0}; pairs=[(j-1,j) for j in range(1,2*s)]
        changed=True
        while changed:
            before=set(current)
            for parity in (0,1):
                for j,(a,b) in enumerate(pairs,1):
                    if j%2==parity and ({a,b}&current): current|={a,b}
            changed=current!=before
        assert current==set(range(2*s))
    print(json.dumps({'kind':'finite diagnostics, not mathematical proof',
        'flag_projection':'unwanted affine tuple verified',
        'density_positive_m3_kappa1':{'sample_cases':positive[0],'violations':positive[1],'flats':positive[2]},
        'density_threshold_mutation_m1_kappa2':{'sample_cases':negative[0],'countercases':negative[1]},
        'common_rank_submodularity':'false as claimed',
        'alternating_closure_path_cases':20},indent=2))

if __name__=='__main__': main()
