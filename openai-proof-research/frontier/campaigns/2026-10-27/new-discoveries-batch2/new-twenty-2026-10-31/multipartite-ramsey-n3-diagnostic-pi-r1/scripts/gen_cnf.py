#!/usr/bin/env python3
"""MathDB 359209 bounded diagnostic: n=3, s=4.

Instance: host K_{3x4} (3 parts, 4 vertices each), 48 independent edge
Boolean variables (red=true), forbid every monochromatic K_{2,3} (injective,
non-induced; two-vertex side may be same-part or cross-part; the three common
neighbors are any eligible vertices outside BOTH endpoint parts).

For each unordered vertex pair {u,v} and each 3-subset T of eligible
neighbors, add:
  - all-red-forbidden clause:  OR of negated the 6 incident edge vars
  - all-blue-forbidden clause: OR positive of the same 6 vars
18 same-part pairs x 2*C(8,3) + 48 cross-part pairs x 2*C(4,3) = 2400 clauses, len 6.

Deterministic ordering: pairs sorted, triples sorted, vars sorted asc,
red clause before blue clause. No symmetry constraints. No dedup applied
(duplicates are validated and reported instead).
"""
import json, hashlib, itertools, os

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
P = 3   # host parts
S = 4   # vertices per part
N = P * S

def part(v): return v // S

# vertices 0..11 = (a,i), a in 0..2, i in 0..3; id = a*4+i
vertices = list(range(N))
edges = []  # (u,v) u<v; host K_{3x4} has only cross-part edges: 3*16=48
for u in range(N):
    for v in range(u + 1, N):
        if part(u) != part(v):
            edges.append((u, v))
assert len(edges) == 48, len(edges)

var_of = {e: i + 1 for i, e in enumerate(edges)}  # 1-based DIMACS; +x = red

pairs = []  # (u,v,eligible list)
for u in range(N):
    for v in range(u + 1, N):
        pu, pv = part(u), part(v)
        elig = [w for w in vertices if part(w) != pu and part(w) != pv]
        pairs.append((u, v, elig))

clauses = []
meta = []
for (u, v, elig) in pairs:
    for T in itertools.combinations(sorted(elig), 3):
        e6 = []
        for w in T:
            e6.append(var_of[(min(u, w), max(u, w))])
            e6.append(var_of[(min(v, w), max(v, w))])
        e6s = sorted(e6)
        # all-red forbidden: at least one of the six edges is not red
        c_red = [-x for x in e6s]
        # all-blue forbidden: at least one of the six edges is red
        c_blue = list(e6s)
        clauses.append(c_red);  meta.append({'pair': [u, v], 'T': list(T), 'kind': 'not-all-red'})
        clauses.append(c_blue); meta.append({'pair': [u, v], 'T': list(T), 'kind': 'not-all-blue'})

# ---- validation ----
same_part_pairs = [p for p in pairs if part(p[0]) == part(p[1])]
cross_part_pairs = [p for p in pairs if part(p[0]) != part(p[1])]
validation = {
    'vertices': N, 'edges': len(edges), 'pairs_total': len(pairs),
    'same_part_pairs': len(same_part_pairs), 'cross_part_pairs': len(cross_part_pairs),
    'clauses': len(clauses),
    'expected_clauses': 2 * (len(same_part_pairs) * len(list(itertools.combinations(range(8), 3)))
                             + len(cross_part_pairs) * len(list(itertools.combinations(range(4), 3)))),
    'all_len6': all(len(c) == 6 for c in clauses),
    'vars_in_range': all(1 <= abs(x) <= 48 for c in clauses for x in c),
    'distinct_vars_per_clause': all(len(set(map(abs, c))) == 6 for c in clauses),
    'no_trivial_tautology': all(len(set(c)) == len(c) for c in clauses),
    'duplicate_clauses': len(clauses) - len({tuple(c) for c in clauses}),
    'duplicate_varsets': len(clauses) - len({tuple(sorted(map(abs, c))) for c in clauses}),
    'completeness_crosscheck': None,
    'no_host_nonedge_used': None,
}
# completeness: independent recount of (pair, triple, color) coverage
cov = set()
for (u, v, elig) in pairs:
    for T in itertools.combinations(sorted(elig), 3):
        for color in ('R', 'B'):
            cov.add((u, v, T, color))
validation['completeness_crosscheck'] = (len(cov) == len(meta) == len(clauses))
# no host nonedge: every literal's edge endpoints in distinct parts
edge_ok = all(part(u) != part(v) for (u, v) in edges)
validation['no_host_nonedge_used'] = edge_ok

# ---- write CNF (DIMACS, deterministic) ----
cnf_path = os.path.join(BASE, 'ramsey_n3_s4.cnf')
with open(cnf_path, 'w') as f:
    f.write(f"c MathDB359209 diagnostic n=3 s=4 host K_3x4 forbid mono K_2,3\n")
    f.write(f"c vars 1..48 = edges (u,v) u<v in id order u*4.. ; + = red\n")
    f.write(f"p cnf 48 {len(clauses)}\n")
    for c in clauses:
        f.write(' '.join(map(str, c)) + ' 0\n')

mapping = {
    'vertices': {'count': N, 'scheme': 'id = part*4 + index, part in 0..2, index in 0..3'},
    'edges': [{'var': var_of[e], 'u': e[0], 'v': e[1]} for e in edges],
    'clause_meta': meta,
    'pair_eligible_counts': {f'{u}-{v}': len(el) for (u, v, el) in pairs},
}
with open(os.path.join(BASE, 'mapping.json'), 'w') as f:
    json.dump(mapping, f, indent=1)

res = {
    'validation': validation,
    'cnf_sha256': hashlib.sha256(open(cnf_path, 'rb').read()).hexdigest(),
    'mapping_sha256': hashlib.sha256(open(os.path.join(BASE, 'mapping.json'), 'rb').read()).hexdigest(),
    'clause_order_hash': hashlib.sha256(
        '\n'.join(' '.join(map(str, c)) for c in clauses).encode()).hexdigest(),
}
with open(os.path.join(BASE, 'cnf-validation.json'), 'w') as f:
    json.dump(res, f, indent=1)
print(json.dumps(validation, indent=1))
print('cnf_sha256', res['cnf_sha256'])
print('clause_order_hash', res['clause_order_hash'])
