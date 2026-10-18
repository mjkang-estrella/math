#!/usr/bin/env python3
"""MIT. Finite interface diagnostics only; not the complete T250P algorithm."""
from itertools import product
import json, random

def graph_checks():
    graphs=pairs=0
    for n in range(1,6):
        for f in product(range(-1,n),repeat=n):
            adj=[set() for _ in range(n)]
            for i,j in enumerate(f):
                if j>=0:adj[i].add(j);adj[j].add(i)
            orbits=[]
            for i in range(n):
                o=set();j=i
                while j>=0 and j not in o:o.add(j);j=f[j]
                orbits.append(o)
            for i in range(n):
                component={i};todo=[i]
                while todo:
                    for j in adj[todo.pop()]-component:component.add(j);todo.append(j)
                for j in range(n):
                    assert (j in component)==bool(orbits[i]&orbits[j]);pairs+=1
            graphs+=1
    return {'partial_functional_graphs':graphs,'vertex_pair_tests':pairs}

def brick_checks():
    rng=random.Random(250);prefixes=['','0','1','00','01','10','11']
    count=empty=0
    def inv(g):return tuple(g.index(i) for i in range(len(g)))
    def apply(a,b,g,x):
        assert all(x[i].startswith(a[i]) for i in range(3))
        tails=[x[i][len(a[i]):] for i in range(3)];gi=inv(g)
        return [b[i]+tails[gi[i]] for i in range(3)]
    for _ in range(10000):
        a,b,c,d=([rng.choice(prefixes) for _ in range(3)] for _ in range(4))
        g=tuple(rng.sample(range(3),3));h=tuple(rng.sample(range(3),3));hi=inv(h)
        if any(not(u.startswith(v) or v.startswith(u)) for u,v in zip(b,c)):
            empty+=1;continue
        e=[max((u,v),key=len) for u,v in zip(b,c)]
        ap=[a[s]+e[g[s]][len(b[g[s]]):] for s in range(3)]
        dp=[d[t]+e[hi[t]][len(c[hi[t]]):] for t in range(3)]
        hg=tuple(h[g[s]] for s in range(3))
        assert sum(map(len,ap))<=sum(map(len,a))+sum(map(len,c))
        assert sum(map(len,dp))<=sum(map(len,b))+sum(map(len,d))
        for _ in range(4):
            x=[ap[i]+''.join(rng.choice('01') for _ in range(16)) for i in range(3)]
            assert apply(c,d,h,apply(a,b,g,x))==apply(ap,dp,hg,x)
            count+=1
    return {'composition_samples':count,'empty_intersections':empty,'seed':250}

def budget_checks():
    count=0
    for D in range(16,65):
        for r in range(1,129):assert 8+2*r<=D*r;count+=1
        for L in range(1,1025):assert 4*(L//D)<L;count+=1
        for N in range(1,257):
            assert 2*((N-1)//D)<2*N+2+8
            assert N-1<2*N+1<2*N+2;count+=1
    for t in range(2,1025):assert 3*t-4>0;count+=1
    # Independent absorption model used solely to exercise the explicit literal branch.
    for w in ['','zeta','azeta','zetaa','a','aa']:
        absorbing_reducible=('zeta' in w and w!='zeta')
        assert absorbing_reducible==(w in ['azeta','zetaa'])
    return {'integer_budget_tests':count,'absorption_examples':6}

if __name__=='__main__':
    print(json.dumps({'status':'PASS','functional_graph':graph_checks(),'brick':brick_checks(),'budget':budget_checks(),'limits':'Finite support checks only; no actual fixed-point compiler or full K/H evaluator implemented.'},indent=2))
