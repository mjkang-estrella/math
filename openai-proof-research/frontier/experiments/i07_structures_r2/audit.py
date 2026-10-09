"""Independent byte audit and exact finite diagnostics; no topology certification.

Writes only frontier/{sources,experiments}/i07_structures_r2/.
Run from any cwd with Python 3. No third-party dependencies.
"""
from pathlib import Path
from itertools import product
from collections import deque
import hashlib
import json

ROOT = Path(__file__).resolve().parents[3]
SOURCE = ROOT / 'frontier/sources/i07_structures'
OUT = ROOT / 'frontier/sources/i07_structures_r2'
EXP = Path(__file__).resolve().parent
OUT.mkdir(parents=True, exist_ok=True)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    return json.loads(path.read_text())


def save(path, obj):
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')


pin = read_json(ROOT / 'sources/upstream.json')['commit']
tree = read_json(ROOT / 'sources/preprints-tree.json')
assert tree['truncated'] is False
entries = tree['tree']
inventory = {e['path']: e for e in entries}
assert len(inventory) == len(entries)
retrieval = read_json(SOURCE / 'retrieval-manifest.json')
records = []
for item in retrieval:
    data = (SOURCE / 'upstream' / item['path']).read_bytes()
    blob = hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()
    indexed = inventory[item['path']]
    checks = {
        'sha256_matches_retrieval': digest(data) == item['sha256'],
        'git_blob_matches_complete_inventory': blob == indexed['sha'],
        'bytes_match_retrieval': len(data) == item['bytes'],
        'bytes_match_inventory': len(data) == indexed['size'],
        'url_is_pinned': item['url'] == f'https://raw.githubusercontent.com/openai/math/{pin}/{item["path"]}',
    }
    records.append(dict(path=item['path'], sha256=digest(data), git_blob_sha1=blob,
                        bytes=len(data), checks=checks))

selected_families = {x['path'].split('/')[1] for x in retrieval}
expected = {e['path'] for e in entries if e['type'] == 'blob'
            and len(e['path'].split('/')) > 1
            and e['path'].split('/')[1] in selected_families
            and Path(e['path']).suffix in {'.tex', '.bib'}}
actual = {x['path'] for x in retrieval}
contracts = []
for c in read_json(SOURCE / 'theorem-contracts.json'):
    path = SOURCE / 'upstream' / c['path']
    data = path.read_bytes()
    statement = '\n'.join(data.decode().splitlines()[c['start_line']-1:c['end_line']])
    checks = {
        'source_sha256': digest(data) == c['source_sha256'],
        'statement_sha256': digest(c['statement'].encode()) == c['statement_sha256'],
        'exact_line_slice': statement == c['statement'],
        'label_in_statement': ('\\label{' + c['label'] + '}') in statement,
        'pinned_url': c['url'] == f'https://raw.githubusercontent.com/openai/math/{pin}/{c["path"]}',
    }
    contracts.append(dict(path=c['path'], label=c['label'], checks=checks))

artifacts = read_json(SOURCE / 'artifact-hashes.json')
artifact_bad = []
for a in artifacts:
    path = ROOT / a['path']
    if not path.is_file() or digest(path.read_bytes()) != a['sha256'] or path.stat().st_size != a['bytes']:
        artifact_bad.append(a['path'])
owned_files = {str(p.relative_to(ROOT)) for folder in [SOURCE, ROOT / 'frontier/experiments/i07_structures']
               for p in folder.rglob('*') if p.is_file() and p != SOURCE / 'artifact-hashes.json'
               and '__pycache__' not in str(p)}
owned_files.add('frontier/iterations/i07-structures.md')
manifest_files = {a['path'] for a in artifacts}
historical = []
for item in read_json(SOURCE / 'input-snapshot.json'):
    path = ROOT / item['path']
    current = digest(path.read_bytes()) if path.is_file() else None
    historical.append(dict(path=item['path'], recorded_sha256=item['sha256'],
                           current_sha256=current, matches=current == item['sha256']))

result = {
    'pin': pin, 'complete_inventory_entries': len(entries),
    'complete_inventory_blobs': sum(e['type'] == 'blob' for e in entries),
    'inventory_truncated': tree['truncated'],
    'retrieved_sources': len(records), 'source_records': records,
    'missing_selected_family_tex_bib': sorted(expected - actual),
    'unexpected_retrieved_paths': sorted(actual - expected),
    'contracts': contracts, 'artifact_count': len(artifacts),
    'artifact_mismatches': artifact_bad,
    'unsealed_original_files': sorted(owned_files - manifest_files),
    'manifest_paths_not_in_original_scope': sorted(manifest_files - owned_files),
    'historical_inputs': historical,
}
result['status'] = 'PASS' if (
    all(all(r['checks'].values()) for r in records + contracts)
    and not expected - actual and not actual - expected
    and not artifact_bad and owned_files == manifest_files) else 'FAIL'
save(OUT / 'provenance-verification.json', result)

# Local endpoint assignments: an n-edge parallel bundle admits a split
# respecting both deficiency bounds exactly when the integer interval is nonempty.
local = []
nonempty = [{0}, {1}, {0, 1}]
for delta, left, right in product(range(2), nonempty, nonempty):
    feasible = True
    for bit in range(2):
        splits = [nleft for nleft in range(6)
                  if (bit not in left or nleft <= 1)
                  and ((bit ^ (1-delta)) not in right or 5-nleft <= 1)]
        feasible &= bool(splits)
    expected_local = (len(left) == len(right) == 1
                      and next(iter(right)) == next(iter(left)) ^ delta)
    assert feasible == expected_local
    local.append(dict(delta=delta, left=sorted(left), right=sorted(right), feasible=feasible))

# All rank-two column-Hermite lattices <(a,0),(b,c)> in a larger range.
# Propagate all r bits together as labels in F_2^r, independently of the supplied script.
lattice_counts = dict(total=0, loopless=0, excluded_loops=0, even_feasible=0, noneven_infeasible=0)
for a in range(1, 13):
    for c in range(1, 13):
        for b in range(a):
            def reduce_vec(v):
                q, y = divmod(v[1], c)
                return ((v[0] - q*b) % a, y)
            lattice_counts['total'] += 1
            if reduce_vec((1, 0)) == (0, 0) or reduce_vec((0, 1)) == (0, 0):
                lattice_counts['excluded_loops'] += 1
                continue
            lattice_counts['loopless'] += 1
            labels = {(0, 0): 0}
            queue = deque([(0, 0)])
            feasible = True
            while queue and feasible:
                v = queue.popleft()
                for j, sign in product(range(2), (-1, 1)):
                    nxt = reduce_vec((v[0] + sign*(j == 0), v[1] + sign*(j == 1)))
                    target = labels[v] ^ (1 << j)
                    if nxt in labels and labels[nxt] != target:
                        feasible = False
                        break
                    if nxt not in labels:
                        labels[nxt] = target
                        queue.append(nxt)
            assert feasible == (a % 2 == b % 2 == c % 2 == 0)
            lattice_counts['even_feasible' if feasible else 'noneven_infeasible'] += 1

# Full endpoint-colored graph realization for small even covers, retaining q
# and both lifts of order-two edges. Actual assignment counts avoid all laws.
cap_results = []
for r in range(1, 7):
    vertices = list(product(range(2), repeat=r))
    counts = {(v, i, c): 0 for v in vertices for i in range(r) for c in range(2)}
    edges = 0
    for v, i, j, bit, q in product(vertices, range(r), range(r), range(2), range(5)):
        w = tuple(x ^ (k == j) for k, x in enumerate(v))
        endbit = bit ^ (i != j)
        selected = (v[i] == bit, w[i] == endbit)
        assert sum(selected) == 1
        recipient, portbit = (w, endbit) if selected[0] else (v, bit)
        counts[(recipient, i, portbit)] += 1
        edges += 1
    assert all(min(counts[v, i, 0], counts[v, i, 1]) <= 1 for v in vertices for i in range(r))
    assert sum(counts.values()) == edges
    n = 10*r
    cap_results.append(dict(rank=r, vertices=len(vertices), edges=edges,
                            bodies=r*n*n*(n-1)*(n-1)*10**4*16))

# All nonzero binary u through rank 8, complement with e_j except first nonzero.
# In these coordinates e_a=u-sum_{j!=a}u_j e_j, and e_j is a complement for j!=a.
lambda_cases = 0
for r in range(1, 9):
    for u in product(range(2), repeat=r):
        if not any(u):
            continue
        a = u.index(1)
        for R in range(1, 13):
            d = 2*R+1
            generators = [tuple(d*x for x in u)] + [tuple(2*(i == j) for i in range(r)) for j in range(r) if j != a]
            assert any(x % 2 for x in generators[0])
            for j in range(r):
                coeff_u = int(j == a)
                complement = [int(j == k) - coeff_u*u[k] for k in range(r) if k != a]
                assert not (coeff_u % d == 0 and all(x % 2 == 0 for x in complement))
            lambda_cases += 1

# A nonsplit test extension: integral Heisenberg group, multiplication
# (a,b,c)*(a',b',c')=(a+a',b+b',c+c'+a*b').
def mul(x, y):
    return x[0]+y[0], x[1]+y[1], x[2]+y[2]+x[0]*y[1]

def inv(x):
    return -x[0], -x[1], -x[2]+x[0]*x[1]

cocycle_cases = 0
for R in range(1, 8):
    d = 2*R+1
    z, h = (d, 0, 0), (0, 2, 0)
    assert mul(mul(mul(z, h), inv(z)), inv(h)) == (0, 0, 2*d)
    for aa, bb, cc, ee in product(range(-3, 4), repeat=4):
        x, y = (d*aa, 2*bb, 0), (d*cc, 2*ee, 0)
        assert mul(x, y) == (d*(aa+cc), 2*(bb+ee), 2*d*aa*ee)
        cocycle_cases += 1

# Independently exhaust all functions on the six-vertex mixed-relation example.
mixed_vertices = list(product(range(3), range(2)))
mixed_index = {v: j for j, v in enumerate(mixed_vertices)}
mixed_generators = [(1, 1), (0, 1)]
mixed_counts = {'own_direction_only': [], 'all_directions': []}
for channel in range(2):
    for mode in mixed_counts:
        count = 0
        for values in product(range(2), repeat=6):
            valid = True
            for v, j in product(mixed_vertices, range(2)):
                if mode == 'own_direction_only' and j != channel:
                    continue
                g = mixed_generators[j]
                nxt = ((v[0]+g[0]) % 3, (v[1]+g[1]) % 2)
                valid &= values[mixed_index[nxt]] == (values[mixed_index[v]] ^ (channel == j))
            count += valid
        mixed_counts[mode].append(count)
assert mixed_counts == {'own_direction_only': [2, 8], 'all_directions': [0, 0]}
assert tuple((3*mixed_generators[0][j]+3*mixed_generators[1][j]) % n
             for j, n in enumerate((3, 2))) == (0, 0)

diagnostics = dict(status='PASS', scope='Exact finite diagnostics; not a proof of the geometric or infinite statements.',
                   local_deficiency_cases=local, rank_two_lattices=lattice_counts,
                   cap_assignments=cap_results, obstruction_lattice_cases=lambda_cases,
                   nonsplit_heisenberg_cocycle_cases=cocycle_cases,
                   mixed_relation_example={'generators_in_Z3_times_Z2': [[1,1],[0,1]],
                                           'orders': [6,2], 'odd_relation': [3,3],
                                           'feasible_function_counts': mixed_counts})
save(EXP / 'checks.json', diagnostics)
inputs = ['AGENTS.md', 'sources/upstream.json', 'sources/preprints-tree.json', 'sources/CONTENTS.md',
          'frontier/iterations/i07-structures.md', 'frontier/sources/i07_structures/theorem-contracts.json',
          'frontier/sources/i07_structures/retrieval-manifest.json',
          'frontier/sources/i07_structures/input-snapshot.json',
          'frontier/sources/i07_structures/artifact-hashes.json']
save(OUT / 'input-hashes.json', [dict(path=p, sha256=digest((ROOT/p).read_bytes()), bytes=(ROOT/p).stat().st_size) for p in inputs])
print(json.dumps(dict(provenance=result['status'], inventory_entries=len(entries), sources=len(records),
                      contracts=len(contracts), artifacts=len(artifacts),
                      artifact_mismatches=artifact_bad,
                      contract_failures=[c for c in contracts if not all(c['checks'].values())],
                      historical_changes=[h['path'] for h in historical if not h['matches']],
                      exact_diagnostics=diagnostics['status'], lattice_counts=lattice_counts,
                      obstruction_lattice_cases=lambda_cases, cocycle_cases=cocycle_cases), indent=2))
assert result['status'] == 'PASS'
