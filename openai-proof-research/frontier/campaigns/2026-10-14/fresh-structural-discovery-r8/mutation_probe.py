#!/usr/bin/env python3
"""Read-only exact bounded exploration, never an all-mutation conclusion.
Myeongjin Kang; no affiliation. MIT.
"""
import collections
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent


def mutate(B, k):
    return tuple(tuple(-B[i][j] if i == k or j == k else B[i][j]
                       + max(B[i][k], 0)*max(B[k][j], 0)
                       - max(-B[i][k], 0)*max(-B[k][j], 0)
                       for j in range(len(B))) for i in range(len(B)))


def acyclic(B):
    n = len(B)
    indeg = [sum(B[i][j] > 0 for i in range(n)) for j in range(n)]
    q = [j for j in range(n) if not indeg[j]]
    count = 0
    while q:
        i = q.pop()
        count += 1
        for j in range(n):
            if B[i][j] > 0:
                indeg[j] -= 1
                if not indeg[j]:
                    q.append(j)
    return count == n


def canonical(B):
    return min(tuple(B[i][j] for i in p for j in p)
               for p in itertools.permutations(range(len(B))))


def main():
    A = tuple(map(tuple, json.loads((ROOT/'chart-diagnostics.json').read_text())[1]['gap_omega']))
    assert all(mutate(mutate(A, k), k) == A for k in range(5))
    assert not acyclic(A)
    assert acyclic(((0, 1, 0), (-1, 0, 1), (0, -1, 0)))
    q = collections.deque([(A, ())])
    seen = {A}
    found = None
    while q and len(seen) < 200000:
        B, word = q.popleft()
        if acyclic(B):
            found = word
            break
        if len(word) >= 10:
            continue
        for k in range(5):
            C = mutate(B, k)
            if max(abs(v) for row in C for v in row) > 10:
                continue
            if C not in seen:
                seen.add(C)
                q.append((C, word+(k,)))
    first = dict(max_depth=10, max_entry=10, labelled_states=len(seen),
                 acyclic_word=found, interpretation='bounded search only')

    q = collections.deque([(A, ())])
    seen = {A}
    found = None
    while q and len(seen) < 30000:
        B, word = q.popleft()
        for i, j, k in itertools.combinations(range(5), 3):
            a, b, c = B[i][j], B[j][k], B[k][i]
            if abs(a) == abs(b) == abs(c) == 2 and a*b > 0 and b*c > 0:
                found = dict(mutation_sequence_zero_based=word,
                             markov_indices_zero_based=(i, j, k), matrix=B)
                break
        if found:
            break
        if len(word) >= 8:
            continue
        for k in range(5):
            C = mutate(B, k)
            if max(abs(v) for row in C for v in row) > 6:
                continue
            if C not in seen:
                seen.add(C)
                q.append((C, word+(k,)))
    fixture = json.loads((ROOT/'mutation-diagnostic.json').read_text())
    assert fixture['search_states'] == len(seen) and fixture['certificate'] == found

    sub = []
    for removed in range(5):
        ids = [i for i in range(5) if i != removed]
        B = tuple(tuple(A[i][j] for j in ids) for i in ids)
        q = collections.deque([B])
        seen = {canonical(B)}
        closed, found_acyclic = True, False
        while q:
            B = q.popleft()
            if acyclic(B):
                found_acyclic, closed = True, False
                break
            for k in range(4):
                C = mutate(B, k)
                if max(abs(v) for row in C for v in row) > 4:
                    closed = False
                    continue
                key = canonical(C)
                if key not in seen:
                    seen.add(key)
                    q.append(C)
            if len(seen) > 2000:
                closed = False
                break
        sub.append(dict(removed=removed, classes=len(seen), closed=closed,
                        found_acyclic=found_acyclic,
                        canonical_matrices=sorted(seen) if closed else []))
    assert sub == json.loads((ROOT/'subquiver-diagnostic.json').read_text())
    print(json.dumps(dict(status='BOUNDED_DIAGNOSTICS_ONLY', acyclic_search=first,
                         markov_search_fixture_matched=True,
                         proper_four_root_subquivers=sub), sort_keys=True, indent=2))


if __name__ == '__main__':
    main()
