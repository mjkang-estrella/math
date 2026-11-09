"""Two-block search for MathDB 347138 (Conjecture 35 of Bang-Jensen, Bessy, Yeo).

D = A u B, D[A] = complete digraph on m vertices, D[B] = semicomplete digraph on b vertices,
plus exactly two arcs A->B and two arcs B->A (with distinct endpoints in A).
Then alpha(D) = 2 (A, B cliques in the underlying graph, some cross pair non-adjacent).
Report (D[B], attachments) with lambda(D) >= 2 and some root in A failing, and test whether
the failure persists as m grows.
"""
import itertools, sys, json
sys.path.insert(0, __import__('os').path.dirname(__file__))
from branching import lam_ge2, has_ns_branching, alpha


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


def make(m, b, Barcs, ins, outs):
    # A = 0..m-1, B = m..m+b-1 ; ins: list of (a, bb) ; outs: list of (bb, a)
    arcs = [(u, v) for u in range(m) for v in range(m) if u != v]
    arcs += [(m + u, m + v) for (u, v) in Barcs]
    arcs += [(a, m + bb) for (a, bb) in ins]
    arcs += [(m + bb, a) for (bb, a) in outs]
    return arcs


if __name__ == '__main__':
    b = int(sys.argv[1])
    m = 3
    hits = 0
    checked = 0
    seen = set()
    for Barcs in semicomplete(b):
        indeg = [sum(1 for (u, v) in Barcs if v == w) for w in range(b)]
        outdeg = [sum(1 for (u, v) in Barcs if u == w) for w in range(b)]
        for e1, e2 in itertools.combinations_with_replacement(range(b), 2):
            for x1, x2 in itertools.combinations_with_replacement(range(b), 2):
                # quick degree feasibility for lambda >= 2
                ind = indeg[:]
                ind[e1] += 1
                ind[e2] += 1
                od = outdeg[:]
                od[x1] += 1
                od[x2] += 1
                if min(ind) < 2 or min(od) < 2:
                    continue
                key = (tuple(sorted(Barcs)), e1, e2, x1, x2)
                if key in seen:
                    continue
                seen.add(key)
                arcs = make(m, b, Barcs, [(0, e1), (1, e2)], [(x1, 0), (x2, 2)])
                if not lam_ge2(m + b, arcs):
                    continue
                checked += 1
                n = m + b
                bad = [s for s in range(m) if not has_ns_branching(n, arcs, s)]
                if bad:
                    # persistence test with larger A
                    pers = []
                    for M in (4, 5, 6):
                        arcs2 = make(M, b, Barcs, [(0, e1), (1, e2)], [(x1, 0), (x2, 2)])
                        pers.append([s for s in range(M) if not has_ns_branching(M + b, arcs2, s)])
                    hits += 1
                    if hits <= 8:
                        print(json.dumps({'b': b, 'Barcs': Barcs, 'entries': [e1, e2], 'exits': [x1, x2],
                                          'bad_roots_m3': bad, 'bad_roots_m4_5_6': pers}), flush=True)
    print('b', b, 'checked', checked, 'hits', hits, flush=True)
