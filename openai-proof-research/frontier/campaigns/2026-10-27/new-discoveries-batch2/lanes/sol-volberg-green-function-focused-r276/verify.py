from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
manifest=json.loads((L/'final-manifest.json').read_text()); n=0
for name,r in manifest.items():
 p=L/name;assert p.stat().st_size==r['bytes'];assert hashlib.sha256(p.read_bytes()).hexdigest()==r['sha256'];n+=1
assert set(manifest)=={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['final-manifest.json','verification-receipt.json']}
refs=json.loads((L/'source-bindings.json').read_text())
for r in refs:assert hashlib.sha256(Path(r['path']).read_bytes()).hexdigest()==r['sha256']
# Independently recheck every successful cached-registry and direct-report input.
count=0
for r in json.loads((L/'registry-screen-inventory.json').read_text()):
 assert hashlib.sha256(Path(r['path']).read_bytes()).hexdigest()==r['sha256'];count+=1
for line in (L/'history-screen.jsonl').read_text().splitlines():
 r=json.loads(line);assert hashlib.sha256(Path(r['path']).read_bytes()).hexdigest()==r['sha256'];count+=1
receipt={'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS_ARTIFACT_INTEGRITY_NOT_SCIENTIFIC_ACCEPTANCE','manifest_entries':n,'source_bindings':len(refs),'screened_reference_postchecks':count,'manifest_sha256':hashlib.sha256((L/'final-manifest.json').read_bytes()).hexdigest(),'original_status':'RETIRED','pivot_status':'HOLD','credit':0}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
