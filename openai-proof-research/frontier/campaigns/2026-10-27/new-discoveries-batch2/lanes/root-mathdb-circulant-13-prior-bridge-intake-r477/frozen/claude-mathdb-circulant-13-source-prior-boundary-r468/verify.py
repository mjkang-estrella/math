"""Independent verifier for lane r468. Read-only except the receipt.

Checks (exit 1 on any mismatch):
 1. manifest.json is the exact set of lane files minus manifest.json and
    verification-receipt.json, with matching sha256/size.
 2. every input-bindings.json ref (absolute original) exists with matching sha256/size.
 3. the r467 intake manifest exact set and the nested r376/r382 manifests against
    their ORIGINAL lane files (no upstream verifier executed).
 4. every http/*.meta.json sha256/size matches its .body; challenge flags are false
    for every body used scientifically.
 5. key result flags: logs/validate_intake.json and logs/bridge_check.json status PASS.
Writes verification-receipt.json (unless --no-receipt).
Integrity PASS is not a mathematics or novelty PASS.
"""
import datetime, hashlib, json, os, sys

LANE = os.path.dirname(os.path.abspath(__file__))
LANES = os.path.dirname(LANE)
INTAKE = os.path.join(LANES, 'root-mathdb-circulant-13-review-intake-r467')
EXC = {'manifest.json', 'verification-receipt.json'}
USED = {'kjm2017-pdf', 'kjm2017-doi', 'springer-shaovesel2015-abs', 'zbmath-l321'}


def h(p):
    with open(p, 'rb') as f:
        return hashlib.sha256(f.read()).hexdigest()


fail = []
counts = {}

m = json.load(open(os.path.join(LANE, 'manifest.json')))
listed = {e['path']: e for e in m['files']}
actual = set()
for r, _, fs in os.walk(LANE):
    for f in fs:
        rel = os.path.relpath(os.path.join(r, f), LANE)
        if rel not in EXC:
            actual.add(rel)
if set(listed) != actual:
    fail.append(['manifest-exactset', sorted(actual - set(listed)), sorted(set(listed) - actual)])
for rel, e in listed.items():
    p = os.path.join(LANE, rel)
    if not os.path.isfile(p) or os.path.getsize(p) != e['size'] or h(p) != e['sha256']:
        fail.append(['manifest-mismatch', rel])
counts['manifest_files'] = len(listed)

b = json.load(open(os.path.join(LANE, 'input-bindings.json')))
for e in b['refs']:
    p = e['path']
    if not os.path.isfile(p) or os.path.getsize(p) != e['size'] or h(p) != e['sha256']:
        fail.append(['binding-mismatch', p])
counts['input_refs'] = len(b['refs'])

im = json.load(open(os.path.join(INTAKE, 'manifest.json')))
il = {e['path'] for e in im['files']}
ia = set()
for r, _, fs in os.walk(INTAKE):
    for f in fs:
        ia.add(os.path.relpath(os.path.join(r, f), INTAKE))
if ia - il - EXC:
    fail.append(['intake-unlisted', sorted(ia - il - EXC)])
for e in im['files']:
    p = os.path.join(INTAKE, e['path'])
    if not os.path.isfile(p) or os.path.getsize(p) != e['size'] or h(p) != e['sha256']:
        fail.append(['intake-mismatch', e['path']])
counts['intake_manifest'] = len(im['files'])
for name in ('claude-mathdb-circulant-13-certificate-review-r376',
             'sol-mathdb-circulant-15-source-prior-review-r382'):
    nm = json.load(open(os.path.join(INTAKE, 'frozen', name, 'manifest.json')))
    for e in nm['files']:
        p = os.path.join(LANES, name, e['path'])
        if not os.path.isfile(p) or os.path.getsize(p) != e['size'] or h(p) != e['sha256']:
            fail.append(['nested-original-mismatch', name, e['path']])
    counts['nested_' + name] = len(nm['files'])

hd = os.path.join(LANE, 'http')
nmeta = 0
for f in sorted(os.listdir(hd)):
    if not f.endswith('.meta.json'):
        continue
    meta = json.load(open(os.path.join(hd, f)))
    body = os.path.join(hd, f[:-len('.meta.json')] + '.body')
    if not os.path.isfile(body) or os.path.getsize(body) != meta['size'] or h(body) != meta['sha256']:
        fail.append(['http-meta-mismatch', f])
    if meta['name'] in USED and (not meta.get('usable') or meta.get('challenge_markers')):
        fail.append(['used-body-not-usable', f])
    nmeta += 1
counts['http_meta'] = nmeta

for log in ('logs/validate_intake.json', 'logs/bridge_check.json'):
    if json.load(open(os.path.join(LANE, log))).get('status') != 'PASS':
        fail.append(['status-not-pass', log])

status = 'PASS' if not fail else 'FAIL'
rec = {'status': status, 'utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
       'counts': counts, 'failures': fail,
       'manifest_sha256': h(os.path.join(LANE, 'manifest.json')),
       'scope': 'integrity only; not a mathematics, novelty or acceptance PASS',
       'recommendation': 'EXCLUDE (root adjudicates)',
       'credit_counts_unchanged': {'additional': 9, 'total': 39, 'next': 40}}
if '--no-receipt' not in sys.argv:
    json.dump(rec, open(os.path.join(LANE, 'verification-receipt.json'), 'w'), indent=1)
print(json.dumps({k: rec[k] for k in ('status', 'counts')}), len(fail))
sys.exit(0 if status == 'PASS' else 1)
