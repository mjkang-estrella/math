from pathlib import Path
import json,hashlib,datetime,subprocess
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'finalmanifest.json').read_text());excluded={'finalmanifest.json','verification-receipt.json'}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-excluded
assert set(m['files'])==actual
assert all(sha(L/n)==h for n,h in m['files'].items())
primary=json.loads((L/'primary-freeze.json').read_text());assert all(sha(Path(x['original']))==sha(L/x['copy'])==x['sha256'] for x in primary)
g=json.loads((L/'guard-binding.json').read_text());assert sha(Path(g['original']))==sha(L/g['copy'])==g['sha256']
rows=json.loads((L/'history-receipt.json').read_text())['records'];assert all(sha(L/x['copy'])==x['sha256'] for x in rows)
drift=[x['original'] for x in rows if not Path(x['original']).exists() or sha(Path(x['original']))!=x['sha256']]
for x in json.loads((L/'index-bindings.json').read_text()):assert sha(L/x['copy'])==x['sha256']
for x in json.loads((L/'context-bindings.json').read_text()):assert sha(L/x['copy'])==x['sha256']
r=subprocess.run(['python',str(L/'checks.py')],capture_output=True,text=True,timeout=20);assert r.returncode==0 and r.stdout==(L/'checks.json').read_text()
assert all(sha(L/n)==h for n,h in m['files'].items())
o=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',manifest_files=len(actual),primary_original_copy_pairs=len(primary),historical_snapshot_copies=len(rows),mutable_live_original_changes=drift,snapshot_scope='No assertion live administrative reports immutable; all snapshot bytes exact',replay_output_identical=True,excluded_explicitly=sorted(excluded),workflow_limits='FAILURES.md deviations remain; integrity PASS does not certify universal mathematics or novelty')
(L/'verification-receipt.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o,indent=2))
