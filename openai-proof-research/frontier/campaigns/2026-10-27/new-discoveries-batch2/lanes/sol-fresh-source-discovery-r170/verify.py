import json,hashlib,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
freeze=json.loads((L/'scientific-freeze.json').read_text())
manifest=json.loads((L/'finalmanifest.json').read_text())
for label,j in [('science',freeze),('manifest',manifest)]:
 for row in j['records']:
  p=L/row['path'];b=p.read_bytes()
  assert len(b)==row['bytes'] and sha(b)==row['sha256'],(label,row['path'])
provenance=json.loads((L/'provenance.json').read_text())
g=provenance['guard'];assert sha(Path(g['path']).read_bytes())==g['sha256']
for row in provenance['http_records']:
 if row.get('status')==200:
  assert sha((L/'sources'/row['name']).read_bytes())==row['sha256']
assert provenance['counts']==dict(additional=9,total=39,next=40,changed=False)
assert json.loads((L/'checks.json').read_text())['status']=='PASS diagnostics only'
assert not json.loads((L/'statement-alias-audit-final.json').read_text())['qualified_original_hits']
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',scientific_records=len(freeze['records']),manifest_records=len(manifest['records']),guard_sha256=g['sha256'],sources_verified=True,limits='Integrity and bounded diagnostics only; no independent mathematical/eligibility/prior-art acceptance')
(L/'manifest-verification.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r))
