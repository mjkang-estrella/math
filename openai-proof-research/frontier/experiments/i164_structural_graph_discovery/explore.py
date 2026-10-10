"""Bounded discovery only. Run with -B; stdout is the only output."""
import itertools
import json
import random


def edges_of_prism(m):
    return sorted({tuple(sorted(e)) for i in range(m) for e in
                   [(i, (i + 1) % m), (m + i, m + (i + 1) % m), (i, m + i)]})


def connected(n, edges, removed=()):
    removed = set(removed)
    adj = [set() for _ in range(n)]
    for a, b in edges:
        if a not in removed and b not in removed:
            adj[a].add(b)
            adj[b].add(a)
    left = set(range(n)) - removed
    if not left:
        return True
    seen = {min(left)}
    todo = list(seen)
    while todo:
        for v in adj[todo.pop()] - seen:
            seen.add(v)
            todo.append(v)
    return seen == left


def three_connected(n, edges):
    return all(connected(n, edges, r) for k in range(3)
               for r in itertools.combinations(range(n), k))


def cycles(n, edges):
    edges = [tuple(e) for e in edges]
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    answer = []

    def rec(unused, matching):
        if not unused:
            rem = set(matching)
            cycle = frozenset(e for e in edges if e not in rem)
            if connected(n, cycle):
                answer.append(cycle)
            return
        a = min(unused)
        for b in adj[a]:
            if b in unused:
                rec(unused - {a, b}, matching + [tuple(sorted((a, b)))])
    rec(set(range(n)), [])
    return answer


def chord_colors(chords):
    adj = [[] for _ in chords]
    for i, (a, b) in enumerate(chords):
        for j, (c, d) in enumerate(chords[:i]):
            if (a < c < b < d) or (c < a < d < b):
                adj[i].append(j)
                adj[j].append(i)
    colors = {}
    for i in range(len(chords)):
        if i in colors:
            continue
        colors[i] = 0
        todo = [i]
        while todo:
            j = todo.pop()
            for k in adj[j]:
                if k not in colors:
                    colors[k] = 1 - colors[j]
                    todo.append(k)
                elif colors[k] == colors[j]:
                    return None
    return [colors[i] for i in range(len(chords))]


def main():
    rng = random.Random(164)
    results = []
    for n in (8, 10, 12, 14, 16, 18, 20, 24):
        rim = {tuple(sorted((i, (i + 1) % n))) for i in range(n)}
        odds = list(range(1, n, 2))
        if n <= 14:
            samples = itertools.permutations(odds)
        else:
            samples = (rng.sample(odds, len(odds)) for _ in range(30000))
        checked = 0
        best = None
        distinct = set()
        for perm in samples:
            chords = sorted(tuple(sorted((a, b))) for a, b in zip(range(0, n, 2), perm))
            key = tuple(chords)
            if key in distinct or rim.intersection(chords):
                continue
            colors = chord_colors(chords)
            if colors is None:
                continue
            edges = sorted(rim.union(chords))
            if not three_connected(n, edges):
                continue
            distinct.add(key)
            checked += 1
            count = len(cycles(n, edges))
            if best is None or count < best["h"]:
                best = dict(n=n, h=count, edges=edges, chords=chords, colors=colors)
        results.append(dict(n=n, checked=checked, best=best))
    print(json.dumps(dict(seed=164, trials_per_large_order=30000, results=results,
                         prisms=[dict(m=m, h=len(cycles(2*m, edges_of_prism(m))))
                                 for m in range(4, 18, 2)]), indent=2))


if __name__ == "__main__":
    main()
