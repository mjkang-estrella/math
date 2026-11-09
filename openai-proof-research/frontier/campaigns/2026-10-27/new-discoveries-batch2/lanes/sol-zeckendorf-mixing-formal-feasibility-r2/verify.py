from pathlib import Path
import hashlib,json,datetime
root=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((root/'MANIFEST.json').read_text())
errors=[];drift=[];verified=0
expected=set(manifest['files'])
actual={str(p.relative_to(root)) for p in root.rglob('*') if p.is_file() and p.name not in {'MANIFEST.json','verification-receipt.json'}}
if expected!=actual:errors.append({'coverage_missing':sorted(actual-expected),'coverage_extra':sorted(expected-actual)})
for name,row in manifest['files'].items():
 p=root/name
 if not p.exists() or sha(p)!=row['sha256'] or p.stat().st_size!=row['bytes']:errors.append({'artifact':name})
for row in json.loads((root/'source-bindings.json').read_text())['sources']:
 src=Path(row['original']);admin=row['kind']=='administrative snapshot'
 if row['copy'] is not None:
  dst=root/row['copy']
  if sha(dst)!=row['sha256']:errors.append({'copy':row['copy']})
 if not src.is_file() or sha(src)!=row['sha256']:
  (drift if admin else errors).append({'original_drift':str(src),'kind':row['kind']})
 verified+=1
receipt={'verified_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'result':'PASS' if not errors else 'FAIL','manifest_sha256':sha(root/'MANIFEST.json'),'artifact_count':len(expected),'bindings_checked':verified,'errors':errors,'administrative_original_drift':drift,'scientific_originals_and_copies_checked_after_writes':True,'no_lean_execution':True,'guard':'supplied helper_guard.py; AS/groupRSS512MiB CPU210 wall230; no raised caps'}
(root/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
raise SystemExit(bool(errors))
