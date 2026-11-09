from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'manifest.json').read_text())
assert 'manifest.json' not in manifest and 'verification-receipt.json' not in manifest
assert set(manifest)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
for p,d in manifest.items():assert h(L/p)==d,p
count=0
for fn in ['freeze.json','immutable-refs.json','library-bindings.json']:
    for row in json.loads((L/fn).read_text()):
        for key in ['original','copy']:assert h(Path(row[key]))==row['sha256'],row[key]
        count+=1
for row in json.loads((L/'retrieval-log.json').read_text()):
    if 'sha256' in row:
        assert h(Path(row['file']))==row['sha256']
        if 'copy' in row:assert h(Path(row['copy']))==row['sha256']
assert json.loads((L/'administrative/ledger.json').read_text())['accepted_count']==9
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h(L/'manifest.json'),'files_verified':len(manifest),'original_copy_bindings_verified':count,'counts':[9,39,40],'administrative_policy':'snapshot only','manifest_excludes':['manifest.json','verification-receipt.json']}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt))
