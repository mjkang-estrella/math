# Read-only administrative integrity check for lane r628 intake (no writes except stdout).
import hashlib, json, os, sys
L = os.path.abspath(sys.argv[1])  # lanes dir
R9 = os.path.join(L, 'root-mathdb-breadth-intake-r629')
R7 = os.path.join(L, 'root-mathdb-curvature-adjudication-r627')
P301 = os.path.join(L, 'pi-mathdb-full-corpus-inventory-r301')
def h(p):
    d = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''): d.update(b)
    return d.hexdigest(), os.path.getsize(p)
fails = []; out = {}
def chk(tag, p, sha, size):
    if not os.path.isfile(p): fails.append((tag, p, 'missing')); return
    s, n = h(p)
    if s != sha or n != size: fails.append((tag, p, s, n, sha, size))
def manifest_check(tag, root, man):
    m = json.load(open(os.path.join(root, man)))
    listed = set()
    for e in m['files']:
        chk(tag, os.path.join(root, e['path']), e['sha256'], e.get('size', e.get('bytes')))
        listed.add(e['path'])
    excl = set(m.get('excluded_exact_paths', []))
    actual = set()
    for dp, dn, fn in os.walk(root):
        for f in fn: actual.add(os.path.relpath(os.path.join(dp, f), root))
    extra = sorted(actual - listed - excl); missing = sorted(listed - actual)
    if extra: fails.append((tag, 'extra', extra[:20], len(extra)))
    if missing: fails.append((tag, 'missing', missing[:20]))
    return len(listed), len(extra)
out['r629_manifest'] = h(os.path.join(R9, 'manifest.json'))
out['r627_manifest'] = h(os.path.join(R7, 'manifest.json'))
out['r629_listed_extra'] = manifest_check('r629', R9, 'manifest.json')
out['r627_listed_extra'] = manifest_check('r627', R7, 'manifest.json')
for tag, R in (('r629', R9), ('r627', R7)):
    b = json.load(open(os.path.join(R, 'bindings.json'))); n = 0
    for e in b:
        chk(tag + '-orig', e['original'], e['sha256'], e['bytes']); chk(tag + '-copy', e['copy'], e['sha256'], e['bytes']); n += 1
    out[tag + '_binding_pairs'] = n
# r627 originals vs r629 frozen copies
for f in os.listdir(os.path.join(R9, 'frozen', 'root-mathdb-curvature-adjudication-r627')):
    a = h(os.path.join(R9, 'frozen', 'root-mathdb-curvature-adjudication-r627', f)); o = h(os.path.join(R7, f))
    if a != o: fails.append(('r627-copy-vs-orig', f, a, o))
# r301 manifest original vs copies
mo = os.path.join(P301, 'manifest.json'); out['r301_manifest'] = h(mo)
for R in (R9, R7):
    if h(os.path.join(R, 'frozen', 'pi-mathdb-full-corpus-inventory-r301', 'manifest.json')) != out['r301_manifest']:
        fails.append(('r301-manifest-copy', R))
if out['r301_manifest'] != ('4da10b6dcd6d56a34399195f26abe9ff13f8c3fd67e88b672fc35db2a2a71e15', 22047): fails.append(('r301-manifest-intake-binding',))
m = json.load(open(mo)); chunks = [e for e in m['files'] if e['path'].startswith('corpus/mathdb-normalized-chunk-')]
for e in chunks: chk('chunk', os.path.join(P301, e['path']), e['sha256'], e['bytes'])
for e in m['frozen_inputs']: chk('frozen_input', os.path.join(P301, e['path']), e['sha256'], e['bytes'])
out['chunks'] = len(chunks); out['frozen_inputs'] = len(m['frozen_inputs'])
# reservation + disjointness
res = json.load(open(os.path.join(R7, 'reserved-ids-r628.json'))); q = json.load(open(os.path.join(R7, 'queue-r628.json')))
ids = res['ids']; qids = [r['mathdb_id'] for r in q]
out['n_ids'] = len(ids); out['queue_match'] = sorted(ids) == sorted(qids) and len(set(ids)) == 50
cov = json.load(open(os.path.join(R9, 'coverage-delta.json'))); covids = set(int(k) for k in cov)
out['coverage_r629'] = len(covids)
cov7 = json.load(open(os.path.join(R7, 'coverage-delta.json'))); out['coverage_r627'] = len(cov7)
r630 = set(json.load(open(os.path.join(R9, 'reserved-ids-r630.json')))['ids'])
act = json.load(open(os.path.join(R9, 'active-breadth-reservations.json')))
others = {}
for a in act: others[a['lane']] = set(a['ids'])
out['active_lanes'] = {k: len(v) for k, v in others.items()}
prot = set(res['protected_ids']); adj = json.load(open(os.path.join(R9, 'adjudications.json')))
adjids = set(int(k) for k in adj)
S = set(ids)
out['disjoint_coverage'] = not (S & covids); out['disjoint_r630'] = not (S & r630)
out['disjoint_protected'] = not (S & prot); out['disjoint_adjudicated'] = not (S & adjids)
out['disjoint_other_lanes'] = {k: not (S & v) for k, v in others.items() if k != res['lane']}
out['own_in_active'] = res['lane'] in others and others[res['lane']] == S
out['adjudicated_subset_protected'] = adjids <= prot
for k in ('disjoint_coverage', 'disjoint_r630', 'disjoint_protected', 'disjoint_adjudicated', 'queue_match'):
    if not out[k]: fails.append(('reservation', k))
if not all(out['disjoint_other_lanes'].values()): fails.append(('reservation', 'other_lanes'))
out['fails'] = fails
print(json.dumps(out, indent=1, default=str))
sys.exit(1 if fails else 0)
