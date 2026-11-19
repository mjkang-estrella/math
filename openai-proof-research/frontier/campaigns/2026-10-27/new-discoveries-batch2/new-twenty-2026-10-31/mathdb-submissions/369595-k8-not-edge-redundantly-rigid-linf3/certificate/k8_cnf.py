#!/usr/bin/env python3
"""Generate the K8 / l_inf^3 CNF from clause provenance records.

This mirrors src/K8Cnf.lean exactly: every clause is produced from a provenance
record by the same rule as `K8.Prov.clause`, with literals in the same order.
The Lean side re-derives each clause it uses from its record by kernel
evaluation, so this script is not trusted; it only has to be deterministic.

Output: <out>.cnf (DIMACS) and <out>.prov.json (one record per clause, in order).
"""
import json, sys
from itertools import permutations

def edge_idx(u, v): return u * (15 - u) // 2 + (v - u - 1)
def col_var(u, v, c): return 1 + 3 * edge_idx(min(u, v), max(u, v)) + c
def sgn_var(u, v): return 85 + edge_idx(min(u, v), max(u, v))
def pos(x): return 2 * x
def neg(x): return 2 * x + 1
PAIRS = [(u, v) for u in range(8) for v in range(8) if u < v]
E4 = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]
PERMS3 = [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]
F, T = False, True
REPS = [
    [(0, 0, F), (1, 0, T), (3, 0, F)],
    [(0, 0, F), (1, 0, T), (3, 1, F)],
    [(0, 0, F), (1, 0, T), (4, 0, F), (5, 0, T)],
    [(0, 0, F), (1, 0, T), (4, 0, F), (5, 1, F)],
    [(0, 0, F), (1, 0, T), (4, 1, F), (5, 1, T)],
    [(0, 0, F), (1, 1, F), (4, 1, T), (5, 0, T)],
    [(0, 0, F), (1, 1, F), (2, 2, F), (3, 2, F), (4, 1, T), (5, 0, F)],
]
ANCHORS = [pos(col_var(0, 1, 0)), pos(col_var(0, 2, 0)), pos(col_var(0, 3, 0)), pos(col_var(0, 4, 1)),
           pos(col_var(0, 5, 1)), pos(col_var(0, 6, 2)), pos(col_var(0, 7, 2)),
           pos(sgn_var(0, 1)), pos(sgn_var(0, 2)), pos(sgn_var(0, 4)), pos(sgn_var(0, 6))]

def bit(S, i): return (S >> i) & 1 == 1

def pat_entry(f, tau, eps, e):
    i, c0, s = e
    a, b = E4[i]
    x, y = f[a], f[b]
    c = tau[c0]
    s2 = s ^ bit(eps, c0)
    sv = s2 ^ (y < x)
    return [neg(col_var(x, y, c)), neg(sgn_var(x, y)) if sv else pos(sgn_var(x, y))]

def clause(rec):
    kind = rec[0]
    if kind == 'alo':
        _, u, v = rec; return [pos(col_var(u, v, c)) for c in range(3)]
    if kind == 'amo':
        _, u, v, a, b = rec; return [neg(col_var(u, v, a)), neg(col_var(u, v, b))]
    if kind == 'cut':
        _, S, k, u, v = rec
        return [pos(col_var(x, y, k)) for (x, y) in PAIRS if bit(S, x) != bit(S, y) and not (x == u and y == v)]
    if kind == 'pat':
        _, r, f, t, eps = rec
        out = []
        for e in REPS[r]: out += pat_entry(f, PERMS3[t], eps, e)
        return out
    if kind == 'anchor':
        return [ANCHORS[rec[1]]]
    raise ValueError(kind)

def valid(rec):
    kind = rec[0]
    if kind == 'alo': return rec[1] < rec[2] < 8
    if kind == 'amo': return rec[1] < rec[2] < 8 and rec[3] < rec[4] < 3
    if kind == 'cut': return 0 < rec[1] < 255 and rec[2] < 3 and rec[3] < rec[4] < 8
    if kind == 'pat':
        _, r, f, t, eps = rec
        return r < 7 and t < 6 and eps < 8 and len(f) == 4 and all(x < 8 for x in f) and len(set(f)) == 4
    if kind == 'anchor': return rec[1] < 11
    return False

def records():
    for u, v in PAIRS: yield ('alo', u, v)
    for u, v in PAIRS:
        for a in range(3):
            for b in range(a + 1, 3): yield ('amo', u, v, a, b)
    for S in range(1, 128):
        for k in range(3):
            for u, v in PAIRS:
                if bit(S, u) != bit(S, v): yield ('cut', S, k, u, v)
    for r in range(7):
        for f in permutations(range(8), 4):
            for t in range(6):
                for eps in range(8): yield ('pat', r, list(f), t, eps)
    for j in range(11): yield ('anchor', j)

def dimacs(l): return l // 2 if l % 2 == 0 else -(l // 2)

def main():
    out = sys.argv[1]
    seen = set(); clauses = []; provs = []
    for rec in records():
        assert valid(rec)
        c = clause(rec)
        key = frozenset(c)
        assert len(key) == len(c)
        if key in seen: continue
        seen.add(key); clauses.append(c); provs.append(rec)
    with open(out + '.cnf', 'w') as fh:
        fh.write(f'p cnf 112 {len(clauses)}\n')
        for c in clauses: fh.write(' '.join(str(dimacs(l)) for l in c) + ' 0\n')
    with open(out + '.prov.json', 'w') as fh:
        for rec in provs: fh.write(json.dumps(rec) + '\n')
    kinds = {}
    for r in provs: kinds[r[0]] = kinds.get(r[0], 0) + 1
    print(len(clauses), 'clauses', kinds)

if __name__ == '__main__':
    main()
