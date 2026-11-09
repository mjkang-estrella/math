"""Independent validation of the r467 intake (no upstream verifier executed).

Checks: (1) intake manifest.json entries vs actual files (size+sha256), and that
the manifest lists every file except itself and verification-receipt.json;
(2) each bindings.json entry: original and copy both exist and match sha/size;
(3) nested frozen r376 and r382 manifests vs their ORIGINAL lane directories.
Writes JSON report to argv[2]; exit 1 on any mismatch.
"""
import hashlib, json, os, sys

intake = sys.argv[1]
out = sys.argv[2]
LANES = os.path.dirname(intake.rstrip('/'))


def h(p):
    d = hashlib.sha256()
    with open(p, 'rb') as f:
        for c in iter(lambda: f.read(1 << 20), b''):
            d.update(c)
    return d.hexdigest()


fail = []
rep = {'intake': intake}
man = json.load(open(os.path.join(intake, 'manifest.json')))
listed = {e['path'] for e in man['files']}
actual = set()
for r, _, fs in os.walk(intake):
    for f in fs:
        actual.add(os.path.relpath(os.path.join(r, f), intake))
for e in man['files']:
    p = os.path.join(intake, e['path'])
    if not os.path.isfile(p):
        fail.append(['missing', e['path']]); continue
    if os.path.getsize(p) != e['size'] or h(p) != e['sha256']:
        fail.append(['mismatch', e['path']])
extra = sorted(actual - listed - {'manifest.json', 'verification-receipt.json'})
if extra:
    fail.append(['unlisted', extra])
rep['manifest_entries'] = len(man['files'])
rep['actual_files'] = len(actual)

b = json.load(open(os.path.join(intake, 'bindings.json')))
nb = 0
for e in b:
    for k in ('original', 'copy'):
        p = e[k]
        if not os.path.isfile(p):
            fail.append(['binding-missing', k, p]); continue
        if os.path.getsize(p) != e['size'] or h(p) != e['sha256']:
            fail.append(['binding-mismatch', k, p])
    nb += 1
rep['bindings_checked'] = nb

for name in ('claude-mathdb-circulant-13-certificate-review-r376',
             'sol-mathdb-circulant-15-source-prior-review-r382'):
    m = json.load(open(os.path.join(intake, 'frozen', name, 'manifest.json')))
    orig = os.path.join(LANES, name)
    bad = 0
    for e in m['files']:
        p = os.path.join(orig, e['path'])
        if not os.path.isfile(p) or os.path.getsize(p) != e['size'] or h(p) != e['sha256']:
            bad += 1; fail.append(['nested-orig-mismatch', name, e['path']])
    rep['nested_' + name] = {'entries': len(m['files']), 'bad': bad}
    # frozen copies present in intake must equal originals
    fdir = os.path.join(intake, 'frozen', name)
    for r, _, fs in os.walk(fdir):
        for f in fs:
            rel = os.path.relpath(os.path.join(r, f), fdir)
            op = os.path.join(orig, rel)
            if not os.path.isfile(op) or h(op) != h(os.path.join(r, f)):
                fail.append(['frozen-copy-differs', name, rel])

rep['failures'] = fail
rep['status'] = 'PASS' if not fail else 'FAIL'
json.dump(rep, open(out, 'w'), indent=1, sort_keys=True)
print(rep['status'], len(fail))
sys.exit(1 if fail else 0)
