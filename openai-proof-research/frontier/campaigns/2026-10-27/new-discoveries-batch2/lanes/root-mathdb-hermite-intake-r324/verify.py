from pathlib import Path
import hashlib, json, re, sys
D = Path(__file__).resolve().parent
F = D / 'frozen/pi-wronskian-hermite-source-hypothesis-r323'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def checks():
    bindings = json.loads((D / 'bindings.json').read_text())
    for r in bindings:
        assert sha(Path(r['original'])) == r['sha256']
        assert sha(D / r['copy']) == r['sha256']
    child = json.loads((F / 'manifest.json').read_text())['payloads']
    assert len(child) == 15
    for r in child:
        assert sha(F / r['path']) == r['sha256']
        assert (F / r['path']).stat().st_size == r['bytes']
    child_files = {str(p.relative_to(F)) for p in F.rglob('*') if p.is_file()}
    assert child_files == {r['path'] for r in child} | {'manifest.json', 'verification-receipt.json'}
    external = []
    for line in (F / 'frozen/input-freeze.txt').read_text().splitlines():
        m = re.fullmatch(r'([0-9a-f]{64})  (.+)', line)
        if m:
            assert sha(D.parent / m[2]) == m[1]
            external.append(m[2])
    assert len(external) == 4
    return {'bindings': len(bindings), 'child_payloads': len(child), 'external_bindings': len(external)}
def payloads():
    return sorted(p for p in D.rglob('*') if p.is_file() and str(p.relative_to(D)) not in {'manifest.json','verification-receipt.json'})
if sys.argv[1] == 'build':
    checks()
    (D / 'manifest.json').write_text(json.dumps([{'path': str(p.relative_to(D)), 'sha256': sha(p)} for p in payloads()],indent=2)+'\n')
else:
    result=checks()
    rows=json.loads((D/'manifest.json').read_text())
    assert {r['path'] for r in rows} == {str(p.relative_to(D)) for p in payloads()}
    for r in rows: assert sha(D/r['path'])==r['sha256']
    result.update(result='PASS',root_payloads=len(rows),scope='Integrity and input bindings, not independent mathematics or live-source clearance')
    (D/'verification-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))
