import hashlib, json, sys
from pathlib import Path
from datetime import datetime, timezone

ROOT = Path(__file__).resolve().parent
NAME = 'claude-mathdb-circulant-13-source-prior-boundary-r468'
CHILD = ROOT / 'frozen' / NAME
EXCLUDED = {'manifest.json', 'verification-receipt.json'}

def read(p):
    return json.loads(p.read_text())

def digest(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1048576), b''):
            h.update(b)
    return h.hexdigest()

def check(p, row):
    assert p.is_file(), str(p)
    assert p.stat().st_size == row['size'], str(p)
    assert digest(p) == row['sha256'], str(p)

def payload(base):
    return {str(p.relative_to(base)) for p in base.rglob('*') if p.is_file() and str(p.relative_to(base)) not in EXCLUDED}

bindings = read(ROOT / 'bindings.json')
assert len(bindings) == 104
for row in bindings:
    check(Path(row['original']), row)
    check(Path(row['copy']), row)

cm = read(CHILD / 'manifest.json')
assert len(cm['files']) == 92
assert {r['path'] for r in cm['files']} == payload(CHILD)
assert payload(ROOT.parent / NAME) == payload(CHILD)
for row in cm['files']:
    check(CHILD / row['path'], row)
    check(ROOT.parent / NAME / row['path'], row)
refs = read(CHILD / 'input-bindings.json')['refs']
assert len(refs) == 72
for row in refs:
    check(Path(row['path']), row)
receipt = read(CHILD / 'verification-receipt.json')
assert receipt['status'] == 'PASS' and not receipt['failures']
assert receipt['manifest_sha256'] == digest(CHILD / 'manifest.json')
assert receipt['credit_counts_unchanged'] == {'additional': 9, 'total': 39, 'next': 40}
metas = list((CHILD / 'http').glob('*.meta.json'))
assert len(metas) == 12
for p in metas:
    meta = read(p)
    check(p.with_name(p.name.replace('.meta.json', '.body')), meta)
    if meta['name'] in {'kjm2017-pdf', 'kjm2017-doi', 'springer-shaovesel2015-abs', 'zbmath-l321'}:
        assert meta.get('usable') and not meta.get('challenge_markers')
assert len(read(ROOT / 'frozen/root-mathdb-breadth-intake-r475/coverage-delta.json')) == 3233

rows = [{'path': rel, 'size': (ROOT / rel).stat().st_size, 'sha256': digest(ROOT / rel)} for rel in sorted(payload(ROOT))]
manifest = {'files': rows, 'excluded_exact_paths': sorted(EXCLUDED)}
if sys.argv[1:] == ['build']:
    (ROOT / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    print('BUILD PASS', len(rows))
elif sys.argv[1:] == ['verify']:
    assert read(ROOT / 'manifest.json') == manifest
    result = {'status': 'PASS', 'utc': datetime.now(timezone.utc).isoformat(), 'original_copy_bindings': len(bindings), 'child_payloads': 92, 'child_input_references': 72, 'http_provenance_entries': 12, 'root_payloads': len(rows), 'reported_review_coverage': 3233, 'accepted_counts': {'additional': 9, 'total': 39, 'next': 40}, 'scope': 'integrity only; no mathematical replay or novelty clearance', 'manifest_sha256': digest(ROOT / 'manifest.json')}
    (ROOT / 'verification-receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))
else:
    raise SystemExit('use build or verify')
