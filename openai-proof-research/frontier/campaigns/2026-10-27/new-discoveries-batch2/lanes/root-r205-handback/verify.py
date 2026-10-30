from pathlib import Path
import hashlib,json,subprocess,sys,shutil,datetime
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r205'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
freeze=[dict(path=str(p),bytes=p.stat().st_size,sha256=sha(p)) for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':freeze},indent=2)+'\n')
m=json.loads((S/'finalmanifest.json').read_text())
assert set(m['excludes'])=={'finalmanifest.json','verification-receipt.json'}
assert {str(p.relative_to(S)) for p in S.rglob('*') if p.is_file()}-set(m['excludes'])==set(m['files'])
for n,h in m['files'].items():assert sha(S/n)==h
rows=json.loads((S/'scientific-freeze.json').read_text())
def originals():
 for r in rows:assert sha(Path(r['original']))==sha(S/r['copy'])==r['sha256'],r['original']
originals()
snapshots=json.loads((S/'active-snapshots.json').read_text())
history=json.loads((S/'history-receipt.json').read_text())['records']
aliases=json.loads((S/'legacy-alias-refresh.json').read_text())['records']
for r in snapshots+history+aliases:assert sha(S/r['copy'])==r['sha256']
drift=[r['original'] for r in snapshots if not Path(r['original']).exists() or sha(Path(r['original']))!=r['sha256']]
shutil.copyfile(S/'checks.py',P/'checks.py')
with (P/'checks.json').open('w') as f:subprocess.run([sys.executable,str(P/'checks.py')],stdout=f,check=True)
assert (P/'checks.json').read_bytes()==(S/'checks.json').read_bytes()
c=json.loads((P/'checks.json').read_text())
assert c['method_controls'][0]['momentcurve_ranks']['Q']==34
assert c['method_controls'][0]['perturbed_rank_mod1009']==35
assert c['method_controls'][1]['perturbed_rank_mod1009']==126
originals()
for r in freeze:
 p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes']
receipt=dict(status='PASS',utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_entries=len(m['files']),original_copy_pairs=len(rows),active_snapshots=len(snapshots),history_snapshots=len(history),reference_alias_snapshots=len(aliases),active_live_drift=drift,frozen_files=len(freeze),private_replay='byte-identical',qualification='Exact rational rank confirms a failed specialization, not a generic counterexample. Full dimension, degree and characteristic scope remains unresolved.')
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
