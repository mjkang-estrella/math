#!/usr/bin/env python3
"""Independent verification of the saved 250-bit lex coloring.

Deliberately does NOT import search.py. Rebuilds the host graph and all 300
vertex pairs with ordinary loops, enumerates eligible common neighbors as
explicit lists, recounts red/blue common-neighbor counts, the exact score,
per-vertex red/blue degrees and part-neighbor rows, and compares against the
saved score. Runs unconditionally, including when score > 0 (score > 0 means
no witness was found in the bounded run; it is never called UNSAT or a proof).
"""
import json, hashlib, os, datetime

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# --- host graph: K_{5x5}, vertices (a,i) -> id 5a+i; edges = cross-part pairs
edges = []
for u in range(25):
    for v in range(u + 1, 25):
        if u // 5 != v // 5:
            edges.append((u, v))
assert len(edges) == 250, len(edges)

adj = {u: set(), }
for u in range(25):
    adj[u] = set()
for e, (u, v) in enumerate(edges):
    adj[u].add(v)
    adj[v].add(u)

# --- all 300 unordered vertex pairs; eligible w by explicit membership tests
pairs = []
for u in range(25):
    for v in range(u + 1, 25):
        elig = []
        for w in range(25):
            if w == u or w == v:
                continue
            if w // 5 == u // 5 or w // 5 == v // 5:
                continue  # must be outside both endpoint parts
            if u not in adj[w] or v not in adj[w]:
                continue  # must be adjacent (cross-part) to both
            elig.append(w)
        pairs.append((u, v, elig))
assert len(pairs) == 300, len(pairs)
same_part = sum(1 for u, v, e in pairs if u // 5 == v // 5)
assert same_part == 50
assert all(len(e) == (20 if u // 5 == v // 5 else 15) for u, v, e in pairs)

# --- load saved coloring
saved = json.load(open(os.path.join(BASE, 'best-bits.json')))
bits_str = saved['bits']
assert len(bits_str) == 250
bits = [c == '1' for c in bits_str]
bits_sha = hashlib.sha256(bits_str.encode()).hexdigest()

red_adj = {u: set() for u in range(25)}
blue_adj = {u: set() for u in range(25)}
for e, (u, v) in enumerate(edges):
    (red_adj if bits[e] else blue_adj)[u].add(v)
    (red_adj if bits[e] else blue_adj)[v].add(u)

# --- full recount over every pair, listing eligible common neighbors
pair_table = []
score = 0
excess_pairs = 0
for pi, (u, v, elig) in enumerate(pairs):
    red_common = sorted(w for w in elig if w in red_adj[u] and w in red_adj[v])
    blue_common = sorted(w for w in elig if w in blue_adj[u] and w in blue_adj[v])
    assert len(red_common) + len(blue_common) <= len(elig)  # mixed-color common neighbors in neither
    exc = max(0, len(red_common) - 4) + max(0, len(blue_common) - 4)
    score += exc
    if exc:
        excess_pairs += 1
    pair_table.append({'pi': pi, 'u': u, 'v': v,
                       'same_part': u // 5 == v // 5,
                       'eligible': len(elig),
                       'red_common': len(red_common),
                       'blue_common': len(blue_common),
                       'excess': exc})

# --- degrees and per-vertex part-neighbor rows
degrees, part_rows = {}, {}
for u in range(25):
    red_deg = len(red_adj[u])
    blue_deg = len(blue_adj[u])
    assert red_deg + blue_deg == len(adj[u])
    row_r, row_b = [], []
    for a in range(5):
        if a == u // 5:
            continue
        row_r.append(sum(1 for w in red_adj[u] if w // 5 == a))
        row_b.append(sum(1 for w in blue_adj[u] if w // 5 == a))
    degrees[u] = {'red': red_deg, 'blue': blue_deg}
    part_rows[u] = {'red_by_part': row_r, 'blue_by_part': row_b}

saved_score = saved['best_score']
match = (score == saved_score)

# cross-check the bits sha against search-result.json when present
sr_path = os.path.join(BASE, 'search-result.json')
sr_sha = None
if os.path.exists(sr_path):
    sr = json.load(open(sr_path))
    sr_sha = sr.get('bits_sha256')

out = {
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'independent': True,
    'method': 'plain-loop rebuild of edges/pairs; explicit eligible-common-neighbor lists; no import of search.py',
    'edges': len(edges), 'pairs_checked': len(pairs),
    'same_part_pairs': same_part, 'cross_part_pairs': len(pairs) - same_part,
    'bits_sha256': bits_sha,
    'search_result_bits_sha256': sr_sha,
    'bits_sha_match': (sr_sha is None or sr_sha == bits_sha),
    'recomputed_score': score,
    'saved_score': saved_score,
    'score_match': match,
    'pairs_with_excess': excess_pairs,
    'max_red_common': max(p['red_common'] for p in pair_table),
    'max_blue_common': max(p['blue_common'] for p in pair_table),
    'red_degree_min': min(d['red'] for d in degrees.values()),
    'red_degree_max': max(d['red'] for d in degrees.values()),
    'pair_count_table': pair_table,
    'degrees': degrees,
    'part_neighbor_rows': part_rows,
    'disclaimer': ('score>0: bounded heuristic run found no zero-violation coloring; '
                   'this is NOT an UNSAT result or lower-bound proof. '
                   'score==0 would still be only an unqualified candidate pending '
                   'source/significance/Lean reviews.'),
}
with open(os.path.join(BASE, 'verification.json'), 'w') as f:
    json.dump(out, f, indent=1)
with open(os.path.join(BASE, 'pair-count-table.json'), 'w') as f:
    json.dump(pair_table, f, indent=1)
print(json.dumps({k: out[k] for k in
                  ('recomputed_score', 'saved_score', 'score_match', 'bits_sha_match',
                   'pairs_with_excess', 'max_red_common', 'max_blue_common',
                   'red_degree_min', 'red_degree_max')}))
