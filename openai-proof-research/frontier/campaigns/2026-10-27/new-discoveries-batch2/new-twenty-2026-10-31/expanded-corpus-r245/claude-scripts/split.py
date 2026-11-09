"""Splittability of cyclic Haar graphs H(n,{0,a,b}) (Basic-Groselj-Grunbaum-Pisanski, MathDB 338716).

Definition 4 of the source: a connected graph G is splittable iff there is a set Sigma, independent
in G^2 (pairwise distance >= 3), with G - Sigma disconnected.
Search: take a smallest component C of G - Sigma; WLOG Sigma = N(C) (a subset of a 2-packing is a
2-packing), C connected, and 2|C| + |N(C)| <= 2n (C is a smallest component, so |C| <= |V - C - N(C)|),
with V - C - N(C) nonempty.  Cyclic Haar graphs are vertex-transitive, so WLOG 0+ in C.
Every vertex of C has at most one neighbour in Sigma (two would be at distance 2).
DFS over C-growth with exact branching; exhaustive (no heuristics).

usage: split.py N_FROM N_TO TAG
For each n, every symbol {0,a,b}, 0<a<b<n, with H connected and girth 6 is classified up to affine
equivalence (S -> uS+t, u unit), and splittability is decided exactly; the splitting set is recorded.
"""
import json
import math
import os
import sys
import time

LANE = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r245'
OUT = os.path.join(LANE, 'outputs', 'claude-split')
sys.setrecursionlimit(10000)


def graph(n, S):
    adj = [[] for _ in range(2 * n)]
    for i in range(n):
        for k in S:
            j = n + (i + k) % n
            adj[i].append(j)
            adj[j].append(i)
    return adj


def girth6(n, S):
    # girth of cyclic Haar graph is 4 iff some difference repeats; >=6 iff all differences distinct
    a, b = S[1], S[2]
    diffs = [a, b, b - a, -a, -b, a - b]
    return len({d % n for d in diffs}) == 6


def connected(n, S):
    return math.gcd(math.gcd(S[1], S[2]), n) == 1


def ball2(adj):
    B = []
    for v in range(len(adj)):
        s = {v}
        for u in adj[v]:
            s.add(u)
            for w in adj[u]:
                s.add(w)
        B.append(s)
    return B


class Found(Exception):
    pass


def splittable(n, S, node_limit=50_000_000):
    adj = graph(n, S)
    V = 2 * n
    B2 = ball2(adj)
    status = [0] * V  # 0 undecided, 1 C, 2 S
    noS = [0] * V     # counter of reasons v cannot be in S
    nodes = [0]
    witness = []

    def rec(queue, qi, nC, nS):
        nodes[0] += 1
        if nodes[0] > node_limit:
            raise RuntimeError('node limit')
        # advance to a C vertex with undecided neighbours
        while qi < len(queue):
            c = queue[qi]
            und = [u for u in adj[c] if status[u] == 0]
            if und:
                break
            qi += 1
        else:
            # closed
            if V - nC - nS > 0:
                witness.append([v for v in range(V) if status[v] == 2])
                raise Found
            return
        c = queue[qi]
        hasS = any(status[u] == 2 for u in adj[c])
        options = [None]
        if not hasS:
            options += [u for u in und if noS[u] == 0]
        for opt in options:
            # apply: opt -> S (if not None), rest of und -> C
            newC = [u for u in und if u != opt]
            if 2 * (nC + len(newC)) + nS + (1 if opt is not None else 0) > V:
                continue
            ok = True
            for u in newC:
                if status[u] != 0:
                    ok = False
            if not ok:
                continue
            for u in newC:
                status[u] = 1
                noS[u] += 1
            if opt is not None:
                status[opt] = 2
                for w in B2[opt]:
                    noS[w] += 1
            # consistency: a C vertex adjacent to two S is prevented by noS; an S adjacent to S likewise
            rec(queue + newC, qi + 1, nC + len(newC), nS + (1 if opt is not None else 0))
            if opt is not None:
                for w in B2[opt]:
                    noS[w] -= 1
                status[opt] = 0
            for u in newC:
                status[u] = 0
                noS[u] -= 1

    status[0] = 1
    noS[0] += 1
    try:
        rec([0], 0, 1, 0)
    except Found:
        return True, witness[0], nodes[0]
    return False, None, nodes[0]


def affine_class(n, S):
    best = None
    units = [u for u in range(1, n) if math.gcd(u, n) == 1]
    for u in units:
        T = [(u * s) % n for s in S]
        for t in T:
            R = tuple(sorted((x - t) % n for x in T))
            if best is None or R < best:
                best = R
    return best


def families(n):
    fam = {}
    if n >= 7:
        fam[affine_class(n, (0, 1, 3))] = 'F1 H(n,{0,1,3})'
    if n % 3 == 0:
        m = n // 3
        if m >= 2 and girth6(n, (0, 1, m)) and connected(n, (0, 1, m)):
            fam.setdefault(affine_class(n, (0, 1, m)), 'F2 H(3m,{0,1,m})')
        if m >= 4 and m % 3 != 0 and girth6(n, (0, 1, m + 1)):
            fam.setdefault(affine_class(n, (0, 1, m + 1)), 'F3 H(3m,{0,1,m+1})')
    return fam


def main():
    os.makedirs(OUT, exist_ok=True)
    a0, a1, tag = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    t0 = time.time()
    res = []
    for n in range(a0, a1 + 1):
        classes = {}
        for a in range(1, n):
            for b in range(a + 1, n):
                S = (0, a, b)
                if not connected(n, S) or not girth6(n, S):
                    continue
                ac = affine_class(n, S)
                classes.setdefault(ac, S)
        fam = families(n)
        rows = []
        for ac, S in sorted(classes.items()):
            sp, wit, nodes = splittable(n, ac)
            rows.append({'symbol': list(ac), 'splittable': sp, 'witness': wit, 'nodes': nodes,
                         'family': fam.get(ac)})
        uns = [r for r in rows if not r['splittable']]
        bad = [r for r in rows if (r['family'] is None) != r['splittable']]
        res.append({'n': n, 'girth6_affine_classes': len(rows), 'splittable': len(rows) - len(uns),
                    'unsplittable': len(uns), 'unsplittable_symbols': [r['symbol'] for r in uns],
                    'families_present': sorted(set(fam.values())), 'mismatch_with_conjecture': bad,
                    'max_nodes': max((r['nodes'] for r in rows), default=0), 'rows': rows})
        print(n, 'classes', len(rows), 'split', len(rows) - len(uns), 'unsplit', len(uns),
              [r['symbol'] for r in uns], 'MISMATCH' if bad else '', 'maxnodes',
              max((r['nodes'] for r in rows), default=0), round(time.time() - t0, 1), flush=True)
        if time.time() - t0 > 80:
            break
    with open(os.path.join(OUT, f'split-{tag}.json'), 'x') as f:
        json.dump(res, f, indent=1)


if __name__ == '__main__':
    main()
