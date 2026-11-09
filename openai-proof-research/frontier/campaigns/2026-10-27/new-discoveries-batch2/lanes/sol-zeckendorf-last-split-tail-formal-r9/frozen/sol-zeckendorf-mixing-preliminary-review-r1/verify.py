from pathlib import Path
import hashlib,json,datetime
out=Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((out/'manifest.json').read_text())
excluded={'manifest.json','verification-receipt.json'}
actual={str(p.relative_to(out)) for p in out.rglob('*') if p.is_file() and p.name not in excluded}
assert actual==set(manifest['files'])
for name,row in manifest['files'].items():
    p=out/name
    assert digest(p)==row['sha256'] and p.stat().st_size==row['bytes'],name
bindings=json.loads((out/'source-bindings.json').read_text())['bindings']
for r in bindings:
    assert digest(Path(r['original']))==r['sha256'],r['original']
    assert digest(out/r['copy'])==r['sha256'],r['copy']
refs=json.loads((out/'immutable-references.json').read_text())
for r in refs:assert digest(Path(r['immutable_reference']))==r['sha256']
assert json.loads((out/'evidence.json').read_text())['status']=='PASS'
receipt={'status':'PASS','utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':digest(out/'manifest.json'),'files_verified':len(actual),'scientific_original_and_copy_pairs_unchanged':len(bindings),'immutable_references_unchanged':len(refs),'administrative':'snapshots only, no equality-to-live requirement','manifest_excludes':sorted(excluded),'execution':'separate guarded final invocation; receipt only write'}
(out/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
