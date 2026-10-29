from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
d=json.loads((P/'provenance.json').read_text())
for s,row in d['files'].items():
 b=(P/s).read_bytes();assert len(b)==row['bytes'] and hashlib.sha256(b).hexdigest()==row['sha256'],s
assert not (P/'PROOF.md').exists()
assert (P/'sources/current-registry-half.lean').read_bytes()==(P/'sources/registry-half.lean').read_bytes()
assert (P/'sources/current-registry-half.md').read_bytes()==(P/'sources/registry-half.md').read_bytes()
print('PASS frozen hashes, identical relevant registry bodies, no PROOF.md')
