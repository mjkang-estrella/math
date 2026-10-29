from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
sha=lambda f:hashlib.sha256(f.read_bytes()).hexdigest()
d=json.loads((p/'provenance.json').read_text())
for name,h in d['artifacts'].items():assert sha(p/name)==h,name
for name in ['exact','scan','audit','fetch','finalize']:
 rows=(p/'logs'/f'{name}-guard.json').read_text().splitlines();v=json.loads(rows[-1]);assert v['guard_exit']==0 and v['reason'] is None
assert not (p/'PROOF.md').exists()
manifest={str(f.relative_to(p)):sha(f) for f in sorted(p.rglob('*')) if f.is_file() and f.name not in ['SHA256SUMS.json','seal.log','seal-guard.json']}
(p/'SHA256SUMS.json').write_text(json.dumps(manifest,indent=2));print('PASS all provenance artifact hashes; five final guards; no PROOF.md;',len(manifest),'sealed files')
