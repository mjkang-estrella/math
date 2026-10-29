#!/usr/bin/env python3
"""Run under the assigned unchanged helper_guard.py. No imported candidate code.

Counting algorithm: exhaust all permutations of the actual incomparability
support after removing universally comparable vertices. No ideal DP, hooks,
comb recurrence, or candidate count routine is used to obtain the count.
"""
from pathlib import Path
from itertools import permutations
from math import prod, factorial
import json

OUT = Path(__file__).resolve().parent

def reach(n, edges):
    graph = [set() for _ in range(n)]
    for a, b in edges:
        graph[a].add(b)
    result = []
    for a in range(n):
        seen, todo = set(), list(graph[a])
        while todo:
            v = todo.pop()
            if v not in seen:
                seen.add(v)
                todo.extend(graph[v] - seen)
        assert a not in seen
        result.append(seen)
    return result

def instance(m, r, j):
    k = 2*m + 1 + r
    # Build by position blocks, then independently impose EVERY value comparison.
    word = list(range(1,m)) + [k-1] + list(range(m+1,k-m)) + [k,m] + list(range(k-m,k-1))
    assert sorted(word) == list(range(1,k+1))
    d, n = k-m, k+(j-1)*(k-m)
    literal = [(t*d+a,t*d+b) for t in range(j) for a in range(k) for b in range(k) if word[a]<word[b]]
    # Position partition, zero based: occurrence t begins at t*d.
    P = [[t*d+a for a in range(m-1)] for t in range(j+1)]
    H = [t*d+m-1 for t in range(j+1)]
    M = [[t*d+m+a for a in range(r)] for t in range(j)]
    Z = [t*d+m+r for t in range(j)]
    C = P[0][:]
    for t in range(j):
        C += [P[t+1][0]] + M[t] + P[t+1][1:]
    assert sorted(C+H+Z) == list(range(n))
    spine = C + H[::-1]
    model = list(zip(spine,spine[1:])) + [(H[t], Z[t]) for t in range(j)]
    R = reach(n,literal)
    assert R == reach(n,model) # Both inclusions, for every pair.
    assert all(R[x] == set(C[i+1:]+H+Z) for i,x in enumerate(C))
    return n, R

def permutation_count(n, R):
    active = [a for a in range(n) if any(a!=b and b not in R[a] and a not in R[b] for b in range(n))]
    assert len(active) <= 9
    # A universally comparable vertex has its exact rank fixed by its lower set.
    fixed = {sum(a in R[b] for b in range(n)):a for a in range(n) if a not in active}
    assert len(fixed)+len(active)==n
    slots = [i for i in range(n) if i not in fixed]
    edges = [(a,b) for a in range(n) for b in R[a]]
    good = 0
    for perm in permutations(active):
        rank = [0]*n
        for i,a in fixed.items(): rank[a]=i
        for i,a in zip(slots,perm): rank[a]=i
        good += all(rank[a]<rank[b] for a,b in edges)
    return good, factorial(len(active))

def main():
    closures = 0
    for m in range(3,9):
        for r in [0,1,2,5]:
            for j in [1,2,3,5,8,12]:
                instance(m,r,j)
                closures += 1
    rows = []
    for m,r in [(3,0),(3,1),(4,0),(5,3)]:
        for j in range(1,6):
            n,R = instance(m,r,j)
            got, attempted = permutation_count(n,R)
            expected = prod(range(1,2*j,2))
            assert got == expected
            rows.append(dict(m=m,r=r,K=2*m+1+r,j=j,n=n,count=got,expected=expected,permutations_tested=attempted))
    result = dict(status='PASS',closure_cases=closures,count_cases=len(rows),rows=rows,
                  method='BFS closure; exhaustive residual permutations with literal full-edge rejection',
                  limits=dict(max_m=8,max_r=5,max_j_closure=12,max_j_count=5,max_residual_permutations=362880),
                  universal_proof=False)
    (OUT/'checker-results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

if __name__ == '__main__': main()
