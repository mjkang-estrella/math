"""Reduced two-block criterion for MathDB 347138 gadgets (any m >= 3 complete-digraph block A).

D[B] semicomplete on b vertices, entries: A->e1, A->e2 (distinct tails in A), exits: tails x1, x2
(B->A arcs to distinct heads).  A root s in A has no non-separating out-branching if for each
used entry e (other entry e'), no out-branching T of D[B] rooted at e has, in D[B]-T,
 e' reaching all of B and every vertex of B reaching {x1, x2}.
(If e1 == e2 the two A->B arcs enter the same vertex; then e = e' .)
lambda(D) >= 2 reduces to the finite cut check over subsets of B (m >= 3).
Reports counts of gadgets, and how many have min in-degree >= 2 inside D[B].
"""
import itertools, sys


def reach(n, arcs, s, rev=False):
    adj = [[] for _ in range(n)]
    for (u, v) in arcs:
        if rev:
            adj[v].append(u)
        else:
            adj[u].append(v)
    seen = {s}
    st = [s]
    while st:
        x = st.pop()
        for y in adj[x]:
            if y not in seen:
                seen.add(y)
                st.append(y)
    return seen


def branchings(b, arcs, r):
    others = [v for v in range(b) if v != r]
    choices = [[u for (u, w) in arcs if w == v] for v in others]
    for pick in itertools.product(*choices):
        par = dict(zip(others, pick))
        ok = True
        for v in others:
            seen = set()
            w = v
            while w != r:
                if w in seen:
                    ok = False
                    break
                seen.add(w)
                w = par[w]
            if not ok:
                break
        if ok:
            yield {(par[v], v) for v in others}


def fails(b, arcs, e, e2, exits):
    full = set(range(b))
    for T in branchings(b, arcs, e):
        R = [a for a in arcs if a not in T]
        if reach(b, R, e2) != full:
            continue
        back = set()
        for x in exits:
            back |= reach(b, R, x, rev=True)
        if back == full:
            return False
    return True


def lam_ok(b, arcs, entries, exits):
    for k in range(0, b + 1):
        for Y in itertools.combinations(range(b), k):
            Y = set(Y)
            Z = set(range(b)) - Y
            internal = sum(1 for (u, v) in arcs if u in Y and v in Z)
            if Z and internal + sum(1 for v in entries if v in Z) < 2:
                return False
            if Y and internal + sum(1 for v in exits if v in Y) < 2:
                return False
    return True


def semicomplete(b):
    pairs = list(itertools.combinations(range(b), 2))
    for states in itertools.product(range(3), repeat=len(pairs)):
        arcs = []
        for (u, v), st in zip(pairs, states):
            if st in (0, 2):
                arcs.append((u, v))
            if st in (1, 2):
                arcs.append((v, u))
        yield arcs


if __name__ == '__main__':
    b = int(sys.argv[1])
    hits = 0
    hits_mindeg2 = 0
    examples = []
    for arcs in semicomplete(b):
        indeg = [sum(1 for (u, v) in arcs if v == w) for w in range(b)]
        for e1, e2 in itertools.combinations_with_replacement(range(b), 2):
            for x1, x2 in itertools.combinations_with_replacement(range(b), 2):
                if not lam_ok(b, arcs, [e1, e2], [x1, x2]):
                    continue
                if fails(b, arcs, e1, e2, [x1, x2]) and fails(b, arcs, e2, e1, [x1, x2]):
                    hits += 1
                    if min(indeg) >= 2:
                        hits_mindeg2 += 1
                        if len(examples) < 5:
                            examples.append((arcs, (e1, e2), (x1, x2)))
    print('b', b, 'hits', hits, 'hits with min in-degree >= 2 in D[B]', hits_mindeg2)
    for ex in examples:
        print(ex)
