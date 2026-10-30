from pathlib import Path
import json,hashlib,datetime,subprocess,sys,os
L=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
def load(n):return json.loads((L/n).read_text())
settled=[]
for r in load('scientific-freeze.json'):
 p=Path(r['original']);c=L/r['copy'];a=sha(p.read_bytes());b=sha(c.read_bytes());assert a==b==r['sha256'],str(p)
 settled.append(str(p))
# Mutable/reference reports: fixed snapshot integrity, live drift is separate.
drift=[]
for r in load('active-snapshots.json'):
 assert sha((L/r['copy']).read_bytes())==r['sha256']
 p=Path(r['original'])
 if not p.exists() or sha(p.read_bytes())!=r['sha256']:drift.append(str(p))
R=L.parents[5];aliases=load('legacy-alias-refresh.json')['records'];alias_drift=[]
for r in aliases:
 assert sha((L/r['copy']).read_bytes())==r['sha256']
 p=R/r['reference_path']
 if not p.exists() or sha(p.read_bytes())!=r['sha256']:alias_drift.append(str(p))
# Every qualified original is accounted for, including active snapshots.
assert len(load('history-receipt.json')['records'])==1532
assert all(Path(x['original']).name.lower() in {'summary.md','discovery.md','proof.md','review.md','decision.md'} for x in load('history-receipt.json')['records'])
p=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,timeout=90,check=True)
assert json.loads(p.stdout)==load('checks.json')
manifest=load('finalmanifest.json');excluded=set(manifest['excludes'])
assert excluded=={'finalmanifest.json','verification-receipt.json'}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in excluded}
assert actual==set(manifest['files'])
for n,h in manifest['files'].items():assert sha((L/n).read_bytes())==h,n
receipt=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS',settled_original_copy_bindings=len(settled),active_snapshot_count=len(load('active-snapshots.json')),active_live_drift=drift,reference_alias_snapshot_count=len(aliases),reference_alias_live_drift=alias_drift,exact_check_replay=True,manifest_files=len(actual),manifest_sha256=sha((L/'finalmanifest.json').read_bytes()),manifest_excludes=sorted(excluded),guard_environment={k:os.environ.get(k) for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','PYTHONDONTWRITEBYTECODE']},limits='No proof or novelty certification. Administrative live originals are not scientifically bound.')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
