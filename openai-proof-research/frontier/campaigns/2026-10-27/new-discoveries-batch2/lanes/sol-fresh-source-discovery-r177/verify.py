"""Independent read-only payload/freeze checker; only its receipt is written."""
import hashlib,json,datetime
from pathlib import Path
L=Path(__file__).resolve().parent
report={}
for n in ['scientific-freeze.json','finalmanifest.json','primary-hashes.json']:
 j=json.loads((L/n).read_bytes());rows=j['records']
 for r in rows:
  p=L/r['path'];assert p.is_file();b=p.read_bytes()
  assert len(b)==r['bytes'] and hashlib.sha256(b).hexdigest()==r['sha256'],r['path']
 report[n]=len(rows)
manifest=json.loads((L/'finalmanifest.json').read_bytes())
listed={r['path'] for r in manifest['records']}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}
assert actual-listed<=set(manifest['exclusions'])
assert 'finalmanifest.json' not in listed and 'manifest-verification.json' not in listed
h=json.loads((L/'history-receipt.json').read_bytes())
assert len(h['records'])==1755 and not h['missing']
assert all(any(f'r{k}/' in r[0] for r in h['records']) for k in [111,112,113])
c=json.loads((L/'checks.json').read_bytes());t=json.loads((L/'tree-route.json').read_bytes())
assert c['graphs']==770 and sum(t['tested'].values())==18247 and not t['failed']
assert not (L/'PROOF.md').exists()
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',verified=report,unlisted_files=sorted(actual-listed),self_and_receipt_exclusions=manifest['exclusions'],scientific_scope='Integrity only; no universal mathematical or novelty PASS.')
(L/'manifest-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
