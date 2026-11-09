from pathlib import Path
import hashlib,json,zipfile
w=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
m=json.loads((w/'dossier-manifest.json').read_text())
for n,v in m['files'].items():assert h((w/n).read_bytes())==v,n
z=w/'frozen/330264-r3-FULL-LEAN.zip'
assert h(z.read_bytes())=='2cab69a4914f29fb3f934b8f57c8807bcb3298bea7e1b535246e9e205e3acaab'
with zipfile.ZipFile(z) as a:
 for n in a.namelist():
  if n.endswith('.lean'):assert (w/'proof'/n).read_bytes()==a.read(n),n
r=json.loads((w/'replay-receipt.json').read_text());assert r['status']=='PASS_FULL_LEAN_ENDPOINT'
assert len(r['builds'])==10 and len(r['axiom_audits'])==24
for audit in r['axiom_audits']:assert set(audit['axioms'])<={'propext','Classical.choice','Quot.sound'}
print('PASS dossier hashes, original archive, unchanged Lean, ten builds and 24 allowed axiom audits')
