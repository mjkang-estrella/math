from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
j=json.loads((p/'provenance.json').read_text())
for x in j['files']:
 d=(p/x['path']).read_bytes()
 assert len(d)==x['bytes'] and hashlib.sha256(d).hexdigest()==x['sha256'],x['path']
assert j['credit']==0 and j['primary_screens']==4
assert not (p/'PROOF.md').exists()
c=json.loads((p/'checks.json').read_text())
assert sum(x['graphs'] for x in c['atlas'])==1251
assert all(not x['violations'] for x in c['atlas'])
for f in ['check-guard.json','exact-guard.json']:
 g=json.loads((p/f).read_text());assert g['guard_exit']==0 and g['reason'] is None
for f in ['sources/current-omega-D5.json','sources/current-omega-Problems.json']:
 assert not json.loads((p/f).read_text())['truncated']
print('PASS hashes, capped diagnostic receipts and no-result scope; no universal proof')
