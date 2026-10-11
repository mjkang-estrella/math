"""Independent I167 graph and exact linear algebra kernel, no ancestor imports."""
from collections import Counter, deque
from functools import lru_cache
from itertools import combinations
from math import gcd


def edge(a, b):
    return tuple(sorted((a, b)))


def edges(faces):
    return tuple(sorted({edge(a, b) for f in faces
                         for a, b in zip(f, f[1:] + f[:1])}))


def adjacency(es):
    out = {}
    for a, b in es:
        out.setdefault(a, set()).add(b)
        out.setdefault(b, set()).add(a)
    return out


def connected(es, vertices=None):
    nb = adjacency(es)
    vs = set(nb) if vertices is None else set(vertices)
    if not vs:
        return True
    reached = {min(vs)}
    todo = list(reached)
    for v in todo:
        for w in nb.get(v, ()):
            if w in vs and w not in reached:
                reached.add(w)
                todo.append(w)
    return reached == vs


def certify(faces):
    es = edges(faces)
    nb = adjacency(es)
    assert all(len(f) == len(set(f)) >= 4 for f in faces)
    assert all(len(ns) == 3 for ns in nb.values())
    darts = Counter((a, b) for f in faces for a, b in zip(f, f[1:] + f[:1]))
    assert all(darts[a, b] == darts[b, a] == 1 for a, b in es)
    successor = {}
    for f in faces:
        for i, v in enumerate(f):
            successor[v, f[i-1]] = f[(i+1) % len(f)]
    for v, ns in nb.items():
        a = min(ns)
        b = successor[v, a]
        c = successor[v, b]
        assert {a, b, c} == ns and successor[v, c] == a
    assert len(nb) - len(es) + len(faces) == 2
    color = {min(nb): 0}
    todo = list(color)
    for v in todo:
        for w in nb[v]:
            if w not in color:
                color[w] = 1-color[v]
                todo.append(w)
            assert color[w] != color[v]
    assert len(color) == len(nb)
    for k in (1, 2):
        for removed in combinations(nb, k):
            assert connected(es, set(nb)-set(removed))
    return len(nb)


def canon(faces):
    """DFS over rooted oriented rotation systems, distinct from I166's BFS."""
    es = edges(faces)
    nb = adjacency(es)
    rot = {}
    for f in faces:
        for i, v in enumerate(f):
            rot[v, f[i-1]] = f[(i+1) % len(f)]
    candidates = []
    for a, b in es:
        for root, first in ((a, b), (b, a)):
            for flip in (False, True):
                labels = {}
                def visit(v, start):
                    if v in labels:
                        return
                    labels[v] = len(labels)
                    ring = [start, rot[v, start], rot[v, rot[v, start]]]
                    if flip:
                        ring = [ring[0], ring[2], ring[1]]
                    for w in ring:
                        visit(w, v)
                visit(root, first)
                order = sorted(labels, key=labels.get)
                candidates.append(tuple(tuple(sorted(labels[w] for w in nb[v]))
                                        for v in order))
    return min(candidates)


def expand(faces, step):
    fi, i, j = step
    f = faces[fi]
    assert i < j and (j-i) % 2 == 0
    # GSW cyclic terminal order is u,v,...,y,x,...,u.
    u, v, y, x = f[i], f[(i+1) % len(f)], f[j], f[(j+1) % len(f)]
    p, q, r, s = range(max(adjacency(edges(faces)))+1,
                       max(adjacency(edges(faces)))+5)
    replacements = {(u, v): [u, p, q], (v, u): [v, q, p],
                    (x, y): [x, r, s], (y, x): [y, s, r]}
    out = []
    for k, face in enumerate(faces):
        if k != fi:
            out.append([z for a, b in zip(face, face[1:]+face[:1])
                        for z in replacements.get((a, b), [a])])
    out += [f[i+1:j+1]+[s, q], f[j+1:]+f[:i+1]+[p, r], [p, q, s, r]]
    return out, (u, v, x, y, p, q, r, s)


def steps(faces):
    return [(k, i, j) for k, f in enumerate(faces)
            for i in range(len(f)) for j in range(i+2, len(f), 2)]


@lru_cache(maxsize=512)
def matchings(es):
    nb = adjacency(es)
    vertices = sorted(nb)
    pos = {v: k for k, v in enumerate(vertices)}
    incident = [[] for _ in vertices]
    for i, (a, b) in enumerate(es):
        incident[pos[a]].append((pos[b], 1 << i))
        incident[pos[b]].append((pos[a], 1 << i))
    result = []
    def visit(left, chosen):
        if not left:
            result.append(chosen)
            return
        # Most constrained unmatched vertex, not first-vertex branching.
        v = min((i for i in range(len(vertices)) if left >> i & 1),
                key=lambda i: sum(bool(left >> j & 1) for j, _ in incident[i]))
        for w, bit in incident[v]:
            if left >> w & 1:
                visit(left ^ (1 << v) ^ (1 << w), chosen | bit)
    visit((1 << len(vertices))-1, 0)
    return tuple(sorted(result))


def selected(es, mask):
    return tuple(e for i, e in enumerate(es) if mask >> i & 1)


@lru_cache(maxsize=512)
def cycles(es):
    full = (1 << len(es))-1
    return tuple(sorted(full ^ m for m in matchings(es)
                        if connected(selected(es, full ^ m))))


def paths(es, a, b):
    nb = adjacency(es)
    idx = {e: i for i, e in enumerate(es)}
    out = []
    n = len(nb)
    def visit(tip, seen, used):
        if tip == b:
            if len(seen) == n:
                out.append(used)
            return
        available = (set(nb)-seen) | {tip}
        for v in available-{tip}:
            if len(nb[v] & available) < (1 if v == b else 2):
                return
        for w in nb[tip]-seen:
            visit(w, seen | {w}, used | (1 << idx[edge(tip, w)]))
    visit(a, {a}, 0)
    return tuple(sorted(out))


def cycles_dfs(es):
    nb = adjacency(es)
    root = min(nb)
    out = set()
    for v in sorted(nb[root]):
        reduced = tuple(e for e in es if e != edge(root, v))
        for p in paths(reduced, root, v):
            p_es = set(selected(reduced, p)) | {edge(root, v)}
            out.add(sum(1 << i for i, e in enumerate(es) if e in p_es))
    return tuple(sorted(out))


def primitive(row):
    g = 0
    for x in row:
        g = gcd(g, x)
    return [x//g for x in row] if g else row


def rank(rows, bound=None):
    """Fraction-free integer elimination. Every operation preserves Q-span."""
    basis = {}
    for original in rows:
        row = list(original)
        for j, old in sorted(basis.items()):
            if row[j]:
                a, b = old[j], row[j]
                row = primitive([a*x-b*y for x, y in zip(row, old)])
        j = next((j for j, x in enumerate(row) if x), None)
        if j is not None:
            basis[j] = primitive(row)
            if bound is not None and len(basis) == bound:
                return len(basis)
    return len(basis)


def differences(masks, width):
    if not masks:
        return []
    base = masks[0]
    return [[((x >> i) & 1)-((base >> i) & 1) for i in range(width)]
            for x in masks[1:]]


def dimension(es, hs=None):
    hs = cycles(es) if hs is None else hs
    return rank(differences(hs, len(es)), len(adjacency(es))//2+1)


def brace(es):
    ms = matchings(es)
    for i, a in enumerate(es):
        for j, b in enumerate(es[:i]):
            if not set(a) & set(b) and not any(m >> i & 1 and m >> j & 1 for m in ms):
                return False
    return True


def nontrivial_cut(es):
    """Independent exhaustive 3-edge deletion test, for small graphs only."""
    vs = set(adjacency(es))
    for triple in combinations(es, 3):
        remaining = tuple(e for e in es if e not in triple)
        if not connected(remaining, vs):
            nb = adjacency(remaining)
            reached = {min(vs)}
            todo = list(reached)
            for v in todo:
                for w in nb.get(v, ()):
                    if w not in reached:
                        reached.add(w)
                        todo.append(w)
            if 1 < len(reached) < len(vs)-1:
                return [list(e) for e in triple]
    return None


def contract_square(es, face, flip):
    nb = adjacency(es)
    terminals = [next(iter(nb[v]-set(face))) for v in face]
    out = [e for e in es if not set(e) & set(face)]
    pair = ((0, 1), (2, 3)) if not flip else ((1, 2), (3, 0))
    new = [edge(terminals[a], terminals[b]) for a, b in pair]
    if any(a == b for a, b in new) or len(set(out+new)) != len(out)+2:
        return None
    out = tuple(sorted(out+new))
    vs = set(adjacency(out))
    if not all(connected(out, vs-set(c)) for k in (0, 1, 2)
               for c in combinations(vs, k)):
        return None
    return out


def isomorphic(es, fs):
    """Small graph adjacency backtracking, independent of embedding codes."""
    a, b = adjacency(es), adjacency(fs)
    if len(a) != len(b):
        return False
    mapping = {}
    def rec():
        if len(mapping) == len(a):
            return True
        v = max(set(a)-mapping.keys(), key=lambda v: len(a[v] & mapping.keys()))
        for w in sorted(set(b)-set(mapping.values())):
            if all((u in a[v]) == (z in b[w]) for u, z in mapping.items()):
                mapping[v] = w
                if rec():
                    return True
                del mapping[v]
        return False
    return rec()


def splice_edges(es1, v, es2, w, permutation):
    n1, n2 = adjacency(es1), adjacency(es2)
    shift = max(n1)+1
    ren = {z: shift+i for i, z in enumerate(sorted(n2))}
    out = [e for e in es1 if v not in e]
    out += [edge(ren[a], ren[b]) for a, b in es2 if w not in (a, b)]
    out += [edge(a, ren[b]) for a, b in zip(sorted(n1[v]), permutation)]
    return tuple(sorted(out))
