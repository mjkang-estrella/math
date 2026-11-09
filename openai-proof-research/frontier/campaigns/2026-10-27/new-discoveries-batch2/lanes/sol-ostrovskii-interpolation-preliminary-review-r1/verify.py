from pathlib import Path
import hashlib,json,datetime,importlib.util

lane=Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
try:
    manifest=json.loads((lane/'manifest.json').read_text())
    actual={str(p.relative_to(lane)) for p in lane.rglob('*') if p.is_file()
            and p.name not in {'manifest.json','verification-receipt.json'}}
    assert actual==set(manifest['files'])
    for name,row in manifest['files'].items():
        p=lane/name
        assert digest(p)==row['sha256'] and p.stat().st_size==row['bytes'],name
    checks.append('complete final manifest contents and exact hashes')
    for row in json.loads((lane/'source-bindings.json').read_text())['references']:
        assert digest(Path(row['path']))==row['sha256'],row['path']
        if 'original' in row:
            assert digest(Path(row['original']))==row['original_sha256']==row['sha256']
    checks.append('all immutable references and PDF originals/copies unchanged')
    for row in json.loads((lane/'evidence/extract-bindings.json').read_text()):
        assert digest(lane/row['path'])==row['sha256']
    checks.append('fresh source extract bindings')
    for line in (lane/'access.jsonl').read_text().splitlines():
        row=json.loads(line)
        if 'sha256' in row:assert digest(lane/'live'/(row['name']+'.body'))==row['sha256']
    checks.append('retained live response hashes')
    spec=importlib.util.spec_from_file_location('independent_checker',lane/'checker.py')
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
    assert m.run()==json.loads((lane/'checker-result.json').read_text())
    checks.append('independent exact rational replay matches retained evidence')
    source=(lane/'evidence/2508.13554v2-pp9-16.txt').read_text()
    for anchor in ['Proposition 6.1.','Corollary 6.1.','Definition 6.1.','Conjecture 6.1.','Conjecture 6.3.']:
        assert anchor in source,anchor
    checks.append('source labels bound to fresh PDF extraction')
    receipt={'status':'PASS','checks':checks}
except Exception as e:
    receipt={'status':'FAIL','checks':checks,'error':repr(e)}
receipt.update(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
               manifest_sha256=digest(lane/'manifest.json'),
               scope='separate guarded verification after final writes; administrative files verified as snapshots only')
(lane/'verification-receipt.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt,indent=2))
if receipt['status']!='PASS':raise SystemExit(1)
