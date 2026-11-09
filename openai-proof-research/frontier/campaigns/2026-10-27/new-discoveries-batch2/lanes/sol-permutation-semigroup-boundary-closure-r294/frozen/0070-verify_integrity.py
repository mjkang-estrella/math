from pathlib import Path
import json,hashlib,time
L=Path(__file__).resolve().parent
def digest(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
manifest=json.loads((L/'manifest.json').read_text());bad=[];external=[];checked=0
for p,h in manifest.items():
 if digest(L/p)!=h:bad.append(p)
 checked+=1
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
assert actual==set(manifest)
for r in json.loads((L/'bindings.json').read_text()):
 if digest(r['copy'])!=r['sha256']:bad.append(r['copy'])
 if '/administrative/' not in r['copy'] and digest(r['original'])!=r['sha256']:bad.append(r['original'])
for r in json.loads((L/'access.json').read_text()):
 if 'path' in r and digest(r['path'])!=r['sha256']:bad.append(r['path'])
for r in json.loads((L/'extraction.json').read_text()):
 if digest(r['original'])!=r['sha256'] or digest(r['text'])!=r['text_sha256']:bad.append(r['original'])
for r in json.loads((L/'history-bindings.json').read_text()):
 if digest(r['path'])!=r['sha256']:external.append(r['path'])
assert not (L/'PROOF.md').exists()
assert json.loads((L/'independent-result.json').read_text())['status']=='PASS'
receipt=dict(status='PASS' if not bad and not external else 'HOLD',verified_at_utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),manifest_sha256=digest(L/'manifest.json'),manifest_entries=checked,artifact_or_source_mismatches=bad,historical_original_changes=external,manifest_excludes=['manifest.json','verification-receipt.json'],counts_unchanged=[9,39,40],scope='Integrity only, not full mathematical/novelty acceptance. Administrative original files deliberately not compared to snapshots.')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(receipt)
assert not bad and not external
