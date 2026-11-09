from pathlib import Path
import hashlib,json,datetime
D=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
errors=[]; original_count=copy_count=0
for r in json.loads((D/'bindings.json').read_text()):
 p=Path(r['original']);original_count+=1
 if sha(p)!=r['sha256']:errors.append('original mismatch '+str(p))
 if r['retained_copy']:
  copy_count+=1
  if sha(Path(r['copy']))!=r['sha256']:errors.append('copy mismatch '+r['copy'])
for r in json.loads((D/'primary-coverage.json').read_text()):
 if sha(D/r['pdf'])!=r['sha256']:errors.append('primary mismatch '+r['pdf'])
manifest=json.loads((D/'manifest.json').read_text())
for r in manifest:
 p=D/r['path']
 if not p.is_file() or sha(p)!=r['sha256'] or p.stat().st_size!=r['bytes']:errors.append('manifest mismatch '+r['path'])
expected={r['path'] for r in manifest}
actual={str(p.relative_to(D)) for p in D.rglob('*') if p.is_file() and p not in [D/'manifest.json',D/'verification-receipt.json']}
if expected!=actual:errors.append('manifest inventory mismatch')
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS' if not errors else 'FAIL','errors':errors,'originals_checked':original_count,'retained_copies_checked':copy_count,'manifest_files':len(manifest),'manifest_sha256':sha(D/'manifest.json'),'administrative_originals_claimed_immutable':False,'scientific_mathematics_certified_by_hash_checks':False}
(D/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
raise SystemExit(bool(errors))
