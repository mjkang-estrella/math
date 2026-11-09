"""Probe for Bang-Jensen--Bessy--Yeo Conjecture 35 (MathDB 347138).

Digraph D: simple (no loops, no parallel arcs; 2-cycles allowed).  alpha(D) = independence
number of the underlying simple graph.  lambda(D) = arc-strong connectivity.
Non-separating out-branching rooted at s: spanning out-arborescence B rooted at s with
D minus A(B) strongly connected.
Random arc-deletion descent from dense digraphs keeping alpha = 2 and lambda >= 2;
report digraphs with a root s having no non-separating out-branching.
"""
import random, sys, itertools, json


def reach(n, adj, s, banned=None):
    seen = {s}
    st = [s]
    while st:
        u = st.pop()
        for v in adj[u]:
            if banned and (u, v) in banned:
                continue
            if v not in seen:
                seen.add(v)
                st.append(v)
    return seen


def strong(n, arcs, banned=None):
    out = [[] for _ in range(n)]
    inn = [[] for _ in range(n)]
    for (u, v) in arcs:
        if banned and (u, v) in banned:
            continue
        out[u].append(v)
        inn[v].append(u)
    return len(reach(n, out, 0)) == n and len(reach(n, inn, 0)) == n


def lam_ge2(n, arcs):
    if not strong(n, arcs):
        return False
    for a in arcs:
        if not strong(n, arcs, {a}):
            return False
    return True


def alpha(n, arcs):
    E = set()
    for (u, v) in arcs:
        E.add((min(u, v), max(u, v)))
    best = 1
    for t in itertools.combinations(range(n), 3):
        if all((t[i], t[j]) not in E for i in range(3) for j in range(i + 1, 3)):
            return 3
    for p in itertools.combinations(range(n), 2):
        if p not in E:
            best = 2
    return best


def has_ns_branching(n, arcs, s):
    ins = [[u for (u, v) in arcs if v == w] for w in range(n)]
    others = [v for v in range(n) if v != s]
    others.sort(key=lambda v: len(ins[v]))
    arcset = list(arcs)
    chosen = {}

    def parent_ok():
        # check B acyclic (all reach s via parents)
        for v in others:
            seen = set()
            w = v
            while w != s:
                if w in seen:
                    return False
                seen.add(w)
                w = chosen[w]
        return True

    def rec(i):
        if i == len(others):
            if not parent_ok():
                return False
            banned = {(chosen[v], v) for v in others}
            return strong(n, arcset, banned)
        v = others[i]
        for u in ins[v]:
            chosen[v] = u
            if rec(i + 1):
                return True
        del chosen[v]
        return False

    return rec(0)


def descend(n, rng):
    arcs = set()
    for u in range(n):
        for v in range(n):
            if u != v and rng.random() < 0.75:
                arcs.add((u, v))
    if alpha(n, arcs) > 2 or not lam_ge2(n, arcs):
        return None
    order = list(arcs)
    rng.shuffle(order)
    for a in order:
        arcs.discard(a)
        if alpha(n, arcs) > 2 or not lam_ge2(n, arcs):
            arcs.add(a)
    if alpha(n, arcs) != 2:
        return None
    return arcs


if __name__ == '__main__':
    n, trials, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    found = 0
    tested = 0
    for t in range(trials):
        arcs = descend(n, rng)
        if arcs is None:
            continue
        tested += 1
        bad = [s for s in range(n) if not has_ns_branching(n, arcs, s)]
        if bad:
            found += 1
            if found <= 5:
                print(json.dumps({'n': n, 'arcs': sorted(arcs), 'bad_roots': bad}), flush=True)
    print('n', n, 'tested', tested, 'with_bad_root', found, flush=True)
