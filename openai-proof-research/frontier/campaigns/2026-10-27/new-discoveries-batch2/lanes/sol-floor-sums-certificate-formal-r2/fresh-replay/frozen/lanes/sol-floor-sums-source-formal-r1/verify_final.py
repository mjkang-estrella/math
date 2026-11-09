from pathlib import Path
import json,hashlib,tarfile
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
excluded={'final-manifest.json','final-verification-receipt.json'}
m=json.loads((L/'final-manifest.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded}
assert actual==set(m)
assert all(sha(L/n)==h for n,h in m.items())
rows=json.loads((L/'freeze.json').read_text())
for r in rows:
    assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256']
ar=json.loads((L/'archive-receipt.json').read_text())
assert sha(L/'source-only.tar.gz')==ar['archive_sha256']
with tarfile.open(L/'source-only.tar.gz') as tar:
    assert set(tar.getnames())==set(ar['members'])
    for n,h in ar['members'].items():
        assert hashlib.sha256(tar.extractfile(n).read()).hexdigest()==h
        assert not n.endswith(('.olean','.ilean','.o','.c'))
for base in [L,L/'fresh-replay']:
    a=json.loads((base/'audit-receipt.json').read_text())
    assert a['component_status']=='PASS' and a['literal_endpoint_status']=='NOT_PROVED'
    p=json.loads((base/'pins.json').read_text())
    assert sha(Path(p['lean']))==p['lean_sha256']
    for r in p['packages']:
        g=Path(p['formal'])/'.lake/packages'/r['name']/'.git'
        h=(g/'HEAD').read_text().strip()
        if h.startswith('ref: '):h=(g/h[5:]).read_text().strip()
        assert h==r['revision']
    assert not list(base.glob('*.olean'))
    for name in ['Reduction','Symmetry','Source','Expansion','Audit']:
        if base!=L:assert sha(base/(name+'.lean'))==sha(L/(name+'.lean'))
assert all(sha(L/n)==h for n,h in m.items())
(L/'final-verification-receipt.json').write_text(json.dumps({'status':'PASS_COMPONENT_ONLY',
 'literal_endpoint':'NOT_PROVED','originals_and_copies_before_after':len(rows),
 'manifest_files':len(m),'manifest_sha256':sha(L/'final-manifest.json'),
 'archive_sha256':ar['archive_sha256'],'fresh_extracted_replay':'PASS_COMPONENT_ONLY',
 'counts_unchanged':[9,39,40],'acceptance':'HOLD'},indent=2)+'\n')
print('separate after-write verification PASS; literal endpoint NOT_PROVED')
