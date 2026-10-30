from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
bad=[]
for r in json.loads((L/'scientific-freeze.json').read_text()):
 if sha(Path(r['original']).read_bytes())!=r['sha256'] or sha((L/r['copy']).read_bytes())!=r['sha256']:bad.append(r)
active=[]
for r in json.loads((L/'active-refresh.json').read_text()):
 assert sha((L/r['copy']).read_bytes())==r['sha256']
 if r['changed']:assert sha((L/r['new_copy']).read_bytes())==r['current_sha256']
 if sha(Path(r['original']).read_bytes())!=r['current_sha256']:active.append(r['original'])
m=json.loads((L/'finalmanifest.json').read_text());mbad=[]
assert m['exclusions']==['finalmanifest.json','verification-receipt.json']
for n,h in m['files'].items():
 if sha((L/n).read_bytes())!=h:mbad.append(n)
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(m['exclusions'])
assert actual==set(m['files'])
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),scientific_original_copy_pass=not bad,scientific_failures=bad,manifest_pass=not mbad,manifest_failures=mbad,manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),manifest_file_count=len(m['files']),active_snapshot_copies_pass=True,active_changed_since_snapshot=sum(x['changed'] for x in json.loads((L/'active-refresh.json').read_text())),active_changed_since_refresh=active,scope='Active documents are mutable snapshots, not immutable original claims; administrative live files intentionally unbound.')
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2))
print(json.dumps(r,indent=2));assert not bad and not mbad
