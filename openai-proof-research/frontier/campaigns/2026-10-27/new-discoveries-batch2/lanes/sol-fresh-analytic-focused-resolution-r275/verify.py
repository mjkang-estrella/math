"""Separate read-only verification, apart from its own receipt; guard required."""
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
H=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
manifest=json.loads((p/'final-manifest.json').read_text())
assert 'final-manifest.json' not in manifest and 'verification-receipt.json' not in manifest
assert set(manifest)=={str(f.relative_to(p)) for f in p.rglob('*') if f.is_file() and f.name not in ('final-manifest.json','verification-receipt.json')}
for rel,h in manifest.items():assert H(p/rel)==h,rel
external=0
for name in ['provenance.json','registry-bindings.json','other-screen-bindings.json']:
    for r in json.loads((p/name).read_text()):
        assert H(Path(r['original']))==r['sha256']
        assert H(Path(r['copy']))==r['sha256']
        external+=1
r=json.loads((p/'history-reference.json').read_text())
assert H(Path(r['path']))==r['sha256']
for r in json.loads((p/'source-access.json').read_text())['frozen_files']:
    assert H(p/r['file'])==r['sha256']
receipt={'status':'PASS','manifest_sha256':H(p/'final-manifest.json'),'files':len(manifest),'original_copy_pairs_reverified':external,'history_index_reverified':True,'scientific_result':'excluded public duplicate; credit zero'}
(p/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
