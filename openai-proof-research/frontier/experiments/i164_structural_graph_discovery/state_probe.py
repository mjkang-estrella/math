"""Exact paired-state diagnostics on even bipyramids, stdout only."""
import itertools
import json


def data(m):
    a, b = m, m + 1
    faces = [(a, i, (i + 1) % m) if i % 2 == 0 else
             (b, (i + 1) % m, i) for i in range(m)]
    root = faces[0]
    faces = faces[1:]
    x = set(range(m + 2)) - set(root)
    states = []

    def rec(j, unused, s):
        if j == len(faces):
            states.append(tuple(s))
        else:
            for v in sorted(set(faces[j]) & unused):
                rec(j + 1, unused - {v}, s + [v])
    rec(0, x, [])

    def forest(s):
        parent = list(range(m + 2))

        def find(v):
            while v != parent[v]:
                v = parent[v]
            return v
        for t, v in zip(faces, s):
            u, w = [z for z in t if z != v]
            u, w = find(u), find(w)
            if u == w:
                return False
            parent[u] = w
        return True

    def cycle_count(r, s):
        nxt = dict(zip(r, s))
        unseen = set(x)
        c = 0
        while unseen:
            c += 1
            u = min(unseen)
            while u in unseen:
                unseen.remove(u)
                u = nxt[u]
        return c

    pairs = [(r, s) for r in states for s in states if all(u != v for u, v in zip(r, s))]
    fs = [s for s in states if forest(s) and any(t == s for _, t in pairs)]
    return dict(m=m, states=len(states), ordered_pairs=len(pairs),
                forest_seconds=len(fs), cmin=min(cycle_count(r, s) for r, s in pairs),
                forest_partner_counts=[sum(t == s for _, t in pairs) for s in fs])


if __name__ == "__main__":
    print(json.dumps([data(m) for m in range(4, 22, 2)], indent=2))
