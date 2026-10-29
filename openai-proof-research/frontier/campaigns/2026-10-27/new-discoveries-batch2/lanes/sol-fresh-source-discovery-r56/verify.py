import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent;d=json.loads((P/'provenance.json').read_text())
for rel,m in d['files'].items():
 b=(P/rel).read_bytes();assert len(b)==m['bytes'] and hashlib.sha256(b).hexdigest()==m['sha256'],rel
assert not (P/'PROOF.md').exists()
for rel in ['guard.json','algebra-guard.json','slices-guard.json','slice-probe-guard.json','certify-guard.json','archive-guard.json']:
 x=json.loads((P/rel).read_text());assert x['guard_exit']==0 and x['reason'] is None,rel
print('PASS',len(d['files']),'artifact hashes; all recorded mathematical helper runs completed under caps; no PROOF.md')
