#!/usr/bin/env python3
"""Exact finite diagnostics for r137 author support; read-only, not a proof gate."""
from fractions import Fraction as Q
from itertools import combinations, product
import json


def rank(n, edges, chosen):
    parent = list(range(n))
    def root(i):
        while parent[i] != i:
            i = parent[i]
        return i
    ans = 0
    for j in chosen:
        u, v = map(root, edges[j])
        if u != v:
            parent[u] = v
            ans += 1
    return ans


def cuts(n, edges):
    return [set(j for j, (u, v) in enumerate(edges)
                if bool(s >> u & 1) != bool(s >> v & 1))
            for s in range(1, 1 << n) if s & 1 and s != (1 << n)-1]


def is_k_union(n, edges, chosen, k):
    if len(chosen) != k*(n-1):
        return False
    for mask in range(1, 1 << n):
        count = sum(bool(mask >> edges[j][0] & 1) and
                    bool(mask >> edges[j][1] & 1) for j in chosen)
        if count > k*(mask.bit_count()-1):
            return False
    return True


def fan(N, k):
    h = (k-1)//2
    t = k-1-h
    edges, A, changed = [], set(), set()
    for i in range(1, N+1):
        for kind, uv, ordinary in [('a', (0, i), h), ('b', (i-1, i), t)]:
            for copy in range(k):
                j = len(edges)
                edges.append(uv)
                if copy < ordinary or (copy == k-1 and i % 2 == 0):
                    A.add(j)
                if kind == 'b' and copy == k-1:
                    changed.add(j)
    return edges, A, changed


def pairings(items):
    if not items:
        yield []
        return
    a = items[0]
    for j in range(1, len(items)):
        b = items[j]
        for rest in pairings(items[1:j]+items[j+1:]):
            yield [(a, b)]+rest


def outer(v):
    return [[a*b for b in v] for a in v]


def main():
    # Four-outcome paired lift, checked exactly including cross-block cancellation.
    a, b = (Q(1,4), Q(1,7)), (Q(-1,5), Q(2,9))
    outcomes = [a+b, a+tuple(-x for x in b), b+a, b+tuple(-x for x in a)]
    avg = [[sum(outer(v)[i][j] for v in outcomes)/4 for j in range(4)]
           for i in range(4)]
    target = [[Q(0) for _ in range(4)] for _ in range(4)]
    for i in range(2):
        for j in range(2):
            target[i][j] = target[i+2][j+2] = (a[i]*a[j]+b[i]*b[j])/2
    assert avg == target
    assert all(sum(x*x for x in v) == sum(x*x for x in a+b) for v in outcomes)

    fan_checks = []
    for N, k in product((2,4,6,8), (1,2,3,4,8)):
        edges, A, changed = fan(N,k)
        E = set(range(len(edges)))
        R = A ^ changed
        assert len(A) == len(E-A) == k*N
        assert is_k_union(N+1, edges, A, k)
        assert not is_k_union(N+1, edges, E-A, k)
        assert is_k_union(N+1, edges, R, k)
        assert is_k_union(N+1, edges, E-R, k)
        assert len(changed) == N
        for i in range(1,N+1):
            incoming = set(range(2*k*(i-1), 2*k*i))
            assert len(R & incoming) == k
            assert len(A & incoming) == k+(1 if i%2==0 else -1)
        cc = cuts(N+1,edges)
        raw = max(Q(abs(2*len(A & c)-len(c)), 2*len(c)) for c in cc)
        damage = max(Q(len(changed & c),len(c)) for c in cc)
        assert raw <= Q(1,k) and damage <= Q(1,k)
        if k%2: assert raw <= Q(1,2*k)
        if k==1:
            assert rank(N+1,edges,A)==N and rank(N+1,edges,E-A)==N-1
        if k==1 and N<=6:
            # Independent exhaustive closest complementary tree calculation.
            good = [set(z) for z in combinations(range(len(edges)),N)
                    if rank(N+1,edges,z)==N and
                    rank(N+1,edges,E-set(z))==N]
            assert min(len(A ^ R0) for R0 in good)==N
        fan_checks.append(dict(N=N,k=k,raw=str(raw),damage=str(damage)))

    # Full rank-tight lattice, maximal chain, and all pair transversals in a fan.
    edges,A,_ = fan(4,1)
    E=set(range(len(edges)))
    tight=[]
    for mask in range(1<<len(edges)):
        F={i for i in E if mask>>i&1}
        if len(F)==2*rank(5,edges,F):tight.append(F)
    chain=[set()]
    while chain[-1] != E:
        chain.append(min((F for F in tight if chain[-1]<F),key=len))
    atoms=[chain[i+1]-chain[i] for i in range(len(chain)-1)]
    assert all(len(D)%2==0 for D in atoms)
    assert all(all(not (F&D) or D<=F for D in atoms) for F in tight)
    pp=[]
    for D in atoms:
        dd=sorted(D); pp += list(zip(dd[::2],dd[1::2]))
    for choices in product((0,1),repeat=len(pp)):
        side={pair[c] for pair,c in zip(pp,choices)}
        assert all(len(side&F)*2==len(F) for F in tight)

    # k=1 K4 pairing obstruction; k=2 parallel pairing repairs the false extension.
    e4=list(combinations(range(4),2)); bad=0
    for pp in pairings(list(range(6))):
        trans=[{pair[c] for pair,c in zip(pp,z)} for z in product((0,1),repeat=3)]
        assert any(rank(4,e4,T)<3 for T in trans)
        bad+=1
    assert bad==15
    e42=[edge for edge in e4 for _ in range(2)]
    pp=[(2*i,2*i+1) for i in range(6)]
    for z in product((0,1),repeat=6):
        side={pair[c] for pair,c in zip(pp,z)}
        assert is_k_union(4,e42,side,2)
        assert is_k_union(4,e42,set(range(12))-side,2)
    print(json.dumps(dict(kind='exact finite author diagnostics, no mathematical gate',
                         paired_covariance=True,fan_cases=fan_checks,
                         tight_sets=len(tight),tight_atoms=len(atoms),
                         K4_pairings_checked=bad,
                         parallel_K4_countercheck=True),indent=2))


if __name__ == '__main__':
    main()
