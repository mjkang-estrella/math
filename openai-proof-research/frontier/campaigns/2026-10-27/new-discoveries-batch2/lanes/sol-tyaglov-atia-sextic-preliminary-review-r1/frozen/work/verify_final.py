from pathlib import Path
import json,hashlib,datetime,subprocess,sys
L=Path(__file__).resolve().parents[1]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'manifest.json').read_text());exclude={'manifest.json','verification-receipt.json'}
assert manifest['excluded']==sorted(exclude)
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and str(p.relative_to(L)) not in exclude}
assert actual==set(manifest['files'])
for n,h in manifest['files'].items():assert sha(L/n)==h,n
bindings=0
for n in ['freeze.json','body-bindings.json']:
 for r in json.loads((L/n).read_text()):
  assert sha(Path(r['original']))==r['sha256'],r['original']
  assert sha(Path(r['copy']))==r['sha256'],r['copy']
  bindings+=1
idx=json.loads(next((L/'frozen').glob('*r213__qualified-original-index.json')).read_text())['records']
for r in idx:assert sha(Path(r['snapshot_reference']))==r['sha256'],r['original']
for r in map(json.loads,(L/'http.jsonl').read_text().splitlines()):
 if 'sha256' in r:assert sha(L/'sources'/r['name'])==r['sha256']
r=subprocess.run([sys.executable,str(L/'work/proof_check.py'),'--verify'],capture_output=True,text=True,check=True)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':sha(L/'manifest.json'),'manifest_files':len(actual),'original_copy_bindings':bindings,'immutable_qualified_history_references':len(idx),'independent_integer_proof_checker':'PASS','admin_policy':'snapshot bytes covered by manifest; live ledger/NEXT not bound','exclusions':sorted(exclude),'limits':'Integrity and exact arithmetic only; not independent mathematical acceptance or novelty clearance.'}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
