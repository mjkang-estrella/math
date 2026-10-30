from pathlib import Path
import hashlib,json,datetime,subprocess,sys
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'finalmanifest.json').read_text());excluded={'finalmanifest.json','verification-receipt.json'}
assert set(m['exclusions'])==excluded
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded}
assert actual==set(m['files']),('manifest member mismatch',actual^set(m['files']))
for n,h in m['files'].items():assert sha(L/n)==h,n
scientific=json.loads((L/'scientific-bindings.json').read_text())
for r in scientific:assert sha(Path(r['original']))==sha(L/r['copy'])==r['sha256'],r
drift=[];snapshots=0
for n in ['qualified-original-index.json','alias-refresh.json']:
 for r in json.loads((L/n).read_text())['records']:
  if r.get('missing'):continue
  p=L/r['copy'] if 'copy' in r else Path(r['snapshot_reference'])
  assert sha(p)==r['sha256'],str(p)
  snapshots+=1
  orig=Path(r['original'])
  if not orig.exists() or sha(orig)!=r['sha256']:drift.append(r['original'])
run=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True,check=True)
assert run.stdout==(L/'checks.json').read_text()
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=sha(L/'finalmanifest.json'),manifest_files=len(actual),scientific_pairs=len(scientific),history_snapshot_references=snapshots,history_live_drift=drift,administrative='snapshot copies only; live ledger/NEXT not scientific inputs',exact_replay='byte-identical checks.json',exclusions=sorted(excluded))
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt))
