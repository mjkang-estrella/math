"""Bounded rational Koszul diagnostic; not a proof of the universal inequality.
Run with PYTHONDONTWRITEBYTECODE=1. Prints JSON, writes nothing.
"""
from fractions import Fraction
from itertools import product, combinations
from random import Random
import json
from interval_betti import interval_betti


def rank(matrix):
    a = [[Fraction(x) for x in row] for row in matrix]
    if not a:
        return 0
    r = 0
    for c in range(len(a[0])):
        pivot = next((i for i in range(r, len(a)) if a[i][c]), None)
        if pivot is None:
            continue
        a[r], a[pivot] = a[pivot], a[r]
        v = a[r][c]
        a[r] = [x / v for x in a[r]]
        for i in range(r + 1, len(a)):
            v = a[i][c]
            if v:
                a[i] = [x - v*y for x, y in zip(a[i], a[r])]
        r += 1
        if r == len(a):
            break
    return r


def koszul(D, box):
    n = len(box)
    out = {}
    for multidegree in product(*(range(a+1) for a in box)):
        bases = [[s for s in combinations(range(n), p)
                  if tuple(multidegree[i] - (i in s) for i in range(n)) in D]
                 for p in range(n+1)]
        ranks = [0]
        for p in range(1, n+1):
            idx = {s: i for i, s in enumerate(bases[p-1])}
            matrix = [[0]*len(bases[p]) for _ in bases[p-1]]
            for c, s in enumerate(bases[p]):
                for q in range(len(s)):
                    t = s[:q] + s[q+1:]
                    if t in idx:
                        matrix[idx[t]][c] = (-1)**q
            ranks.append(rank(matrix))
        ranks.append(0)
        for p in range(n+1):
            v = len(bases[p])-ranks[p]-ranks[p+1]
            if v:
                key = p, sum(multidegree)
                out[key] = out.get(key, 0)+v
    return out


def stable_sets(box):
    n = len(box)
    E = sorted(product(*(range(a) for a in box)), key=lambda u: (sum(u), u))
    out = []
    def walk(i, A):
        if i == len(E):
            out.append(frozenset(A))
            return
        u = E[i]
        walk(i+1, A)
        pred = {tuple(u[j]-(j == h) for j in range(n))
                for h in range(n) if u[h]}
        pred.update(tuple(u[j]-(j == h)+(j == l) for j in range(n))
                    for h in range(n) for l in range(h+1, n)
                    if u[h] and u[l]+1 < box[l])
        if pred <= A:
            A.add(u)
            walk(i+1, A)
            A.remove(u)
    walk(0, set())
    return out


if __name__ == '__main__':
    rng = Random(142)
    records = []
    for box in [(2, 2, 2), (2, 2, 3), (3, 3, 3), (2, 2, 2, 2)]:
        sets = stable_sets(box)
        pairs = [(A, B) for A in sets for B in sets if B <= A]
        sample = rng.sample(pairs, min(30, len(pairs)))
        for A, B in sample:
            got = interval_betti(A, B, box)
            expected = koszul(A-B, box)
            if got != expected:
                raise AssertionError((box, A, B, got, expected))
        records.append({'box': box, 'pairs_checked': len(sample)})
    print(json.dumps({'field': 'Q', 'seed': 142, 'comparison': 'recursion vs direct Koszul',
                      'records': records, 'checks': sum(x['pairs_checked'] for x in records)}, indent=2))
