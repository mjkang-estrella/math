#!/usr/bin/env python3
"""Exact finite diagnostics; not certificates of the asymptotic assertions."""
import json
from collections import Counter, deque
from fractions import Fraction as F
from itertools import product


def absorption():
    fibers = [list(range(0, 2)), list(range(2, 5)), list(range(5, 9)), list(range(9, 12))]
    owner = {a: x for x, fs in enumerate(fibers) for a in fs}
    rev = {}
    for a, b in [(0, 2), (1, 5), (3, 9), (4, 6), (7, 10), (8, 11)]:
        rev[a], rev[b] = b, a
    sets = [{x for x in range(4) if mask >> x & 1} for mask in range(16)]
    cases = tight_positive = 0
    maxratio = F(0)
    for A in sets[1:]:
        atoms = [a for x in A for a in fibers[x]]
        restricted = {a: rev[a] if owner[rev[a]] in A else a for a in atoms}
        assert Counter(restricted.values()) == Counter(atoms)
        assert all(restricted[restricted[a]] == a for a in atoms)
        r = max(F(sum(owner[rev[a]] not in A for a in fibers[x]), len(fibers[x])) for x in A)
        if r == 1:
            continue
        def eps(S, T):
            return max([F(sum(owner[rev[a]] not in T for a in fibers[x]), len(fibers[x])) for x in A & S] or [F(0)])
        for U, V, W in product(sets, repeat=3):
            if not U <= V:
                continue
            p = F(sum(owner[a] in U - W for a in atoms), len(atoms))
            lhs, rhs = (1-r)*p, eps(U,V)+eps(V,W)
            assert lhs <= rhs
            cases += 1
            tight_positive += int(lhs == rhs and lhs > 0)
            if rhs:
                maxratio = max(maxratio, lhs/rhs)
    # Conditional original law on A={0,1} is (2/5,3/5).
    # The unique accepted mark at each vertex leads to the other vertex.
    A = {0, 1}
    law = [F(2,5), F(3,5)]
    acceptance = [F(1,2), F(1,3)]
    output = [law[1], law[0]]
    stationary = [law[i]*acceptance[i] for i in range(2)]
    stationary = [s/sum(stationary) for s in stationary]
    assert output != law and stationary == [F(1,2), F(1,2)]
    return dict(fiber_sizes=list(map(len,fibers)), cases=cases, tight_positive=tight_positive,
                largest_ratio=str(maxratio), retry_input=list(map(str,law)),
                retry_output=list(map(str,output)), retry_stationary=list(map(str,stationary)))


def ball(G, roots, radius):
    seen = set(roots)
    layer = set(roots)
    for _ in range(radius):
        layer = set().union(*(G[v] for v in layer))-seen if layer else set()
        seen |= layer
    return seen


def no_short_cycle(G, g):
    for root in range(len(G)):
        dist, parent = {root: 0}, {root: -1}
        q = deque([root])
        while q:
            u = q.popleft()
            for v in G[u]:
                if v == parent[u]:
                    continue
                if v in dist:
                    if dist[u]+dist[v]+1 <= g:
                        return False
                elif dist[u]+1 <= g//2:
                    dist[v], parent[v] = dist[u]+1, u
                    q.append(v)
    return True


def switches():
    L = 24
    def idx(x,y,s): return 2*((x%L)*L+y%L)+s
    G = [set() for _ in range(2*L*L)]
    for x,y in product(range(L),repeat=2):
        u = idx(x,y,0)
        for v in [idx(x,y,1),idx(x-1,y,1),idx(x,y-1,1)]:
            G[u].add(v); G[v].add(u)
    assert all(len(s)==3 for s in G)
    assert len(ball(G,[0],len(G)))==len(G)
    assert no_short_cycle(G,5) and not no_short_cycle(G,6)
    T = ball(G,[0],1)
    boundary = sorted((u,v) for u in T for v in G[u] if v not in T)
    assert len(boundary)==6 and len({u for u,v in boundary})==3
    forbidden = ball(G,{v for e in boundary for v in e},5)
    far = []
    for u in range(len(G)):
        for v in sorted(G[u]):
            if u < v and u not in forbidden and v not in forbidden:
                far.append((u,v))
                forbidden |= ball(G,[u,v],5)
                break
        if len(far)==len(boundary): break
    assert len(far)==6
    for mask in range(64):
        H = [s.copy() for s in G]
        selected = [i for i in range(6) if mask>>i&1]
        for i in selected:
            l,a = boundary[i]; b,c = far[i]
            for u,v in [(l,a),(b,c)]: H[u].remove(v); H[v].remove(u)
        for i in selected:
            l,a = boundary[i]; b,c = far[i]
            for u,v in [(l,c),(a,b)]:
                assert u!=v and v not in H[u]
                H[u].add(v); H[v].add(u)
        assert all(len(s)==3 for s in H) and no_short_cycle(H,5)
        for i in selected:
            l,a = boundary[i]; b,c = far[i]
            for u,v in [(l,c),(a,b)]: H[u].remove(v); H[v].remove(u)
        for i in selected:
            l,a = boundary[i]; b,c = far[i]
            for u,v in [(l,a),(b,c)]: H[u].add(v); H[v].add(u)
        assert H==G
    def walks(G,root,k):
        v=Counter({root:1}); out=[1]
        for _ in range(k):
            w=Counter()
            for u,c in v.items():
                for t in G[u]: w[t]+=c
            v=w; out.append(v[root])
        return out
    tree=[set()]; layers=[[0]]
    for depth in range(6):
        nxt=[]
        for u in layers[-1]:
            for _ in range(3 if u==0 else 2):
                v=len(tree); tree.append({u}); tree[u].add(v); nxt.append(v)
        layers.append(nxt)
    tw=walks(tree,0,6); gw=walks(G,0,6)
    assert gw[:6]==tw[:6] and gw[6]>tw[6]
    # Both color classes and several translates independently checked.
    assert all(walks(G,r,6)==gw for r in [1,2,27,138,751,1151])
    return dict(vertices=len(G),degree=3,girth=6,subsets=64,boundary=boundary,far_edges=far,
                graph_walks=gw,tree_walks=tw,shared_boundary_vertices=3)


def potential_and_same_H():
    before=Counter(product(range(3),repeat=4))
    after=Counter()
    for x,y,e,f in before:
        after[((x+e)%3,(y+f)%3,e,f)]+=1
    assert after==before
    bad=Counter((1 if x==0 else x) for x in range(3))
    assert bad != Counter(range(3))
    a,d=[F(1,5),F(4,5)],[F(4,5),F(1,5)]
    # Two independent Bernoulli observations conditional on the same latent H.
    aa=dd=ad=F(0)
    for h,x,y,r,s in product(range(2),range(2),range(2),range(2),range(2)):
        pr=F(1,2)*(a[h] if x else 1-a[h])*(a[h] if y else 1-a[h])*(d[h] if r else 1-d[h])*(d[h] if s else 1-d[h])
        aa+=pr*x*y; dd+=pr*r*s; ad+=pr*x*r
    square=sum((a[i]-d[i])**2 for i in range(2))/2
    assert aa+dd-2*ad==square==F(9,25)
    assert sum(a)==sum(d)
    return dict(product_atoms=len(before),root_excluded_maps_preserve=True,
                invalid_central_selection_counts=dict(bad),annealed_means_equal=True,
                same_H_second_moment=str(aa),prediction_second_moment=str(dd),
                mixed_moment=str(ad),quenched_squared_error=str(square))


def budgets():
    chi=F(1,8); tau=chi/200000
    exponents={'first_cut':F(15)-100,'schur_signed':6*tau-chi/100,
        'schur_square':6*tau-F(1,200),'schur_mixed':F(13,2)*tau-F(1,200),
        'schur_theta':F(13,2)*tau-F(1,2),'trace_cut':3*tau-F(1,100),
        'replacement':-F(44,100)+F(3,2)*tau,
        'upper_time_ratio':-F(3,4)+101*tau}
    assert all(v<0 for v in exponents.values())
    assert 49*tau>0
    # Exact resolvent sign and regularization kernel, no floating differences.
    eigenvalues=[F(-3),F(-1),F(0),F(2),F(3)]
    E=F(1,3); eta=F(2,5)
    derivative=sum(eta/((t-E)**2+eta**2) for t in eigenvalues)/len(eigenvalues)
    assert derivative>0
    return dict(chi=str(chi),tau=str(tau),negative_exponents={k:str(v) for k,v in exponents.items()},
                lower_time_ratio=str(49*tau),positive_logpotential_derivative=str(derivative))


def run():
    return {'status':'PASS_FINITE_DIAGNOSTICS_ONLY','absorption':absorption(),
            'connected_shared_boundary_switches':switches(),
            'conditional_potentials_and_same_H':potential_and_same_H(),'rational_budgets':budgets()}

if __name__=='__main__': print(json.dumps(run(),indent=2,sort_keys=True))
