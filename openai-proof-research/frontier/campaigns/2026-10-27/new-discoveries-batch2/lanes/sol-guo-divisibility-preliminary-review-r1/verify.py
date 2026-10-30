"""Separate guarded post-write verification; receipt intentionally outside manifest."""
from pathlib import Path
import hashlib,json,datetime
h=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((h/'final-manifest.json').read_text());bad=[]
assert m['explicit_exclusions']==['final-manifest.json','final-verification.json']
assert not any(x in m['files'] for x in m['explicit_exclusions'])
for n,v in m['files'].items():
 if not (h/n).is_file() or sha(h/n)!=v:bad.append(n)
actual={str(p.relative_to(h)) for p in h.rglob('*') if p.is_file()}-set(m['explicit_exclusions'])
if actual!=set(m['files']):bad.append('file inventory mismatch')
f=json.loads((h/'freeze-before.json').read_text())
for x in f['scientific_pairs']:
 if sha(Path(x['original']))!=x['sha256'] or sha(h/x['copy'])!=x['sha256']:bad.append(x['original'])
for line in (h/'retrieval.jsonl').read_text().splitlines():
 x=json.loads(line)
 if 'sha256' in x and sha(h/'live'/x['name'])!=x['sha256']:bad.append('live/'+x['name'])
r=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not bad else 'FAIL',manifest_sha256=sha(h/'final-manifest.json'),verified_manifest_files=len(m['files']),original_copy_pairs=len(f['scientific_pairs']),originals_and_copies_unchanged=not bad,failures=bad,explicit_exclusions=m['explicit_exclusions'],administrative_originals='Not live-bound; snapshots only',scope='Byte integrity only, not a universal proof or novelty certificate')
(h/'final-verification.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r));assert not bad
