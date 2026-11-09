#!/usr/bin/env python3
"""Independent verifier for the n=3,s=4 diagnostic SAT model.

Does NOT trust counts or the solver: re-parses the CNF, regenerates the edge
 numbering in lex order, and checks all 66 vertex pairs for the
 no-monochromatic-K_{2,3} condition via common-neighbor counts.
"""
import json, itertools, hashlib, datetime, os

BASE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

res = json.load(open(os.path.join(BASE, 'solver-result.json')))
assert res['result'] == 'SAT' and res['model_satisfies_cnf'] is True
bits = {int(k): bool(v) for k, v in res['witness_bits'].items()}
assert sorted(bits) == list(range(1, 49)) and len(bits) == 48

# --- independent CNF parse and satisfaction check ---
clauses = []
nvars = None
for line in open(os.path.join(BASE, 'ramsey_n3_s4.cnf')):
    line = line.strip()
    if not line or line[0] in 'cp%':
        if line.startswith('p'):
            nvars = int(line.split()[2])
        continue
    clauses.append([int(x) for x in line.split() if int(x) != 0])
assert nvars == 48 and len(clauses) == 2400
cnf_ok = all(any((l > 0) == bits[abs(l)] for l in c) for c in clauses)

# --- regenerate edge numbering in lex order (host: complete tripartite 3x4) ---
pair2var = {}
v = 1
for u in range(12):
    for w in range(u + 1, 12):
        if u // 4 != w // 4:
            pair2var[(u, w)] = v
            v += 1
assert v == 49 and len(pair2var) == 48

# cross-check regenerated numbering against mapping.json entries
map_ok = True
var2pair = {val: key for key, val in pair2var.items()}
for e in json.load(open(os.path.join(BASE, 'mapping.json')))['edges']:
    if var2pair.get(e['var']) != (e['u'], e['v']):
        map_ok = False
        break

def col(u, w):
    a, b = (u, w) if u < w else (w, u)
    return 'R' if bits[pair2var[(a, b)]] else 'B'

# --- all 66 pairs: common neighbors outside both endpoint parts; both-red/both-blue <= 2 ---
pair_counts = {}
all_le2 = True
for a, b in itertools.combinations(range(12), 2):
    common = [w for w in range(12) if w // 4 != a // 4 and w // 4 != b // 4]
    r = sum(1 for w in common if col(a, w) == 'R' and col(b, w) == 'R')
    bl = sum(1 for w in common if col(a, w) == 'B' and col(b, w) == 'B')
    pair_counts['%d-%d' % (a, b)] = {'common': len(common), 'both_red': r, 'both_blue': bl}
    if r > 2 or bl > 2:
        all_le2 = False

out = {
    'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'cnf_sha256': hashlib.sha256(open(os.path.join(BASE, 'ramsey_n3_s4.cnf'), 'rb').read()).hexdigest(),
    'model_bits': {str(k): bits[k] for k in sorted(bits)},
    'cnf_all_2400_satisfied': cnf_ok,
    'edge_regen_matches_mapping': map_ok,
    'pair_check_rule': ('both_red<=2 and both_blue<=2 over common neighbors outside endpoint '
                        'parts; equivalent to no monochromatic K_{2,3} in the 2-coloring of '
                        'the complete tripartite host K_{4,4,4}, any 2-side/3-side orientation'),
    'all_66_pairs_within_2': all_le2,
    'pair_counts': pair_counts,
}
with open(os.path.join(BASE, 'verification.json'), 'w') as f:
    json.dump(out, f, indent=1)

print('cnf_ok', cnf_ok, 'map_ok', map_ok, 'all_le2', all_le2)
print('max both_red', max(x['both_red'] for x in pair_counts.values()),
      'max both_blue', max(x['both_blue'] for x in pair_counts.values()))
print('common-neighbor sizes seen:', sorted({x['common'] for x in pair_counts.values()}))
