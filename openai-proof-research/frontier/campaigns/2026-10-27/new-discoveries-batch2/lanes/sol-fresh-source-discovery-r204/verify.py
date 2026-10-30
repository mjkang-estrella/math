from pathlib import Path
import json,hashlib,datetime,subprocess,sys
L=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
primary=json.loads((L/'primary-freeze.json').read_text())
errors=[]
for x in primary+[json.loads((L/'guard-binding.json').read_text())]:
 if sha(Path(x['original']))!=x['sha256'] or sha(L/x['copy'])!=x['sha256']:errors.append(x['original'])
manifest=json.loads((L/'finalmanifest.json').read_text())
assert manifest['exclusions']==['finalmanifest.json','verification-receipt.json']
for n,h in manifest['files'].items():
 if sha(L/n)!=h:errors.append(n)
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in manifest['exclusions']}
assert actual==set(manifest['files'])
drift=[];snapshots=0
for x in json.loads((L/'history-receipt.json').read_text())['records']+json.loads((L/'alias-refresh.json').read_text())['records']:
 assert sha(L/x['copy'])==x['sha256'];snapshots+=1
 p=Path(x['original'])
 if not p.exists() or sha(p)!=x['sha256']:drift.append(str(p))
p=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True,check=True)
assert json.loads(p.stdout)==json.loads((L/'checks.json').read_text())
rec=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not errors else 'FAIL',original_copy_errors=errors,primary_bindings=len(primary),manifest_files=len(manifest['files']),manifest_sha256=sha(L/'finalmanifest.json'),report_snapshot_copies_checked=snapshots,live_mutable_report_drift=drift,report_drift_is_scientific_error=False,checker_replay='PASS',manifest_exclusions=manifest['exclusions'],limits='Guarded final verification after final writes; no certificate of novelty or mathematical completeness')
(L/'verification-receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec,indent=2));assert not errors
