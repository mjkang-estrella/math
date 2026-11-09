from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
bound=json.loads((L/'bindings.json').read_text())
for row in bound:
    assert sha(Path(row['original']))==row['sha256']==sha(L/row['copy']),row
refs=json.loads((L/'immutable-source-references.json').read_text())
for row in refs:
    assert sha(Path(row['original']))==row['sha256']==sha(Path(row['copy'])),row
manifest=json.loads((L/'manifest.json').read_text());listed=set()
for row in manifest['files']:
    p=L/row['path'];assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes'],row
    listed.add(row['path'])
assert listed=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in manifest['excludes']}
assert not any(p.suffix=='.lean' for p in L.rglob('*'))
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(L/'manifest.json'),'manifest_members':len(listed),'scientific_original_copy_pairs':len(bound),'immutable_primary_reference_pairs':len(refs),'administrative':'snapshot bytes verified, not compared to mutable shared originals','separate_guarded_invocation':True,'scientific_validity':'integrity verification only; no independent review or formal certification implied'}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
