from pathlib import Path
import hashlib,json,subprocess,sys,datetime,resource,os
l=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((l/'manifest.json').read_text())
assert 'manifest.json' not in manifest and 'verification-receipt.json' not in manifest
actual={str(p.relative_to(l)) for p in l.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
assert actual==set(manifest)
for name,h in manifest.items():assert sha(l/name)==h,name
for r in json.loads((l/'body-bindings.json').read_text()):assert sha(l/r['original'])==sha(l/r['copy'])==r['sha256']
for r in json.loads((l/'freeze-history.json').read_text()):assert sha(Path(r['original']))==sha(Path(r['copy']))==r['sha256']
idx=json.loads((l/'sources/qualified-original-index.json').read_text())
for r in idx['records']:assert sha(Path(r['snapshot_reference']))==r['sha256']
for r in json.loads((l/'catalogue-screen.json').read_text()):assert sha(Path(r['original']))==sha(l/r['copy'])==r['sha256']
cp=subprocess.run([sys.executable,str(l/'checks/check.py')],capture_output=True,text=True,check=True)
assert json.loads(cp.stdout)['PASS']
assert resource.getrlimit(resource.RLIMIT_AS)[0]==512*1024*1024
assert resource.getrlimit(resource.RLIMIT_CPU)[0]==210
for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','PYTHONDONTWRITEBYTECODE']:assert os.environ[k]=='1'
# Check mathematical/source files did not change during replay.
for name,h in manifest.items():assert sha(l/name)==h,name
receipt={'PASS':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(l/'manifest.json'),'files_verified':len(manifest),'immutable_history_references_verified':len(idx['records']),'source_pairs_verified':len(json.loads((l/'body-bindings.json').read_text())),'rational_math_replay':json.loads(cp.stdout),'limits_checked':{'AS_MiB':512,'CPU_s':210},'notes':'separate guarded verifier; no current-registry/novelty/acceptance certification'}
(l/'verification-receipt.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt,indent=2))
