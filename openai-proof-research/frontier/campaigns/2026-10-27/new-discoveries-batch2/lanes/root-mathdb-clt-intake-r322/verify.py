from pathlib import Path
import hashlib, json, sys

D = Path(__file__).resolve().parent
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def checks():
    rows = json.loads((D / 'bindings.json').read_text())
    for r in rows:
        assert sha(Path(r['original'])) == r['sha256']
        assert sha(D / r['copy']) == r['sha256']
    f = D / 'frozen/pi-weighted-clt-source-hypothesis-r313'
    m = json.loads((f / 'MANIFEST.json').read_text())
    for r in m['files']:
        p = f / r['path']
        assert sha(p) == r['sha256'] and p.stat().st_size == r['bytes']
    return {'bindings': len(rows), 'child_payloads': len(m['files'])}
if sys.argv[1] == 'build':
    checks()
    files = sorted(p for p in D.rglob('*') if p.is_file() and p.name not in {'manifest.json', 'verification-receipt.json'})
    (D / 'manifest.json').write_text(json.dumps([{'path': str(p.relative_to(D)), 'sha256': sha(p)} for p in files], indent=2) + '\n')
else:
    result = checks()
    rows = json.loads((D / 'manifest.json').read_text())
    for r in rows:
        assert sha(D / r['path']) == r['sha256']
    actual = {str(p.relative_to(D)) for p in D.rglob('*') if p.is_file() and p.name not in {'manifest.json', 'verification-receipt.json'}}
    assert actual == {r['path'] for r in rows}
    result.update(result='PASS', root_files=len(rows), scope='Delivered byte integrity only; not mathematical or primary-source verification')
    (D / 'verification-receipt.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))
