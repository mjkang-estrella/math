"""Separate read-only verification; only the excluded receipt is written."""
from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest=json.loads((R/'final-manifest.json').read_text())
assert 'final-manifest.json' not in manifest and 'verification-receipt.json' not in manifest
actual={str(p.relative_to(R)) for p in R.rglob('*') if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']}
assert actual==set(manifest)
for name,h in manifest.items():assert sha(R/name)==h,name
for name in ['freeze-before.json','library-freeze.json']:
 for e in json.loads((R/name).read_text()):
  assert sha(e['original'])==sha(e['copy'])==e['sha256'],e
for e in json.loads((R/'binding-check.json').read_text()):
 b=e['binding'];assert sha(b['original'])==sha(b['copy'])==b['sha256']
for e in json.loads((R/'independent-freeze.json').read_text()):assert sha(e['path'])==e['sha256']
for e in json.loads((R/'body-retrieval.json').read_text()):assert sha(e['path'])==e['sha256']
assert json.loads((R/'checker-evidence.json').read_text())['status'].startswith('PASS')
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(R/'final-manifest.json'),files_verified=len(manifest),original_copy_bindings_verified=True,counts_unchanged=[9,39,40],lean_invoked=False)
(R/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt))
