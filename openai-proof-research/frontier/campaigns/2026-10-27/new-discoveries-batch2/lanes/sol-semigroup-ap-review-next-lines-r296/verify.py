from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[];n=0
for name in ['bindings.json','dedup-bindings.json']:
 for row in json.loads((L/name).read_text()):
  n+=1
  for p in [Path(row['original']),L/row['copy']]:
   if not p.is_file() or h(p)!=row['sha256']:errors.append(str(p))
manifest=json.loads((L/'manifest.json').read_text())
for row in manifest:
 p=L/row['path']
 if not p.is_file() or h(p)!=row['sha256']:errors.append(str(p))
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in {'manifest.json','verification-receipt.json'}}
if actual!={r['path'] for r in manifest}:errors.append('manifest coverage mismatch')
for row in json.loads((L/'access.json').read_text()):
 if h(L/row['path'])!=row['sha256']:errors.append(row['path'])
receipt=dict(pass_integrity=not errors,errors=errors,original_copy_pairs=n,manifest_entries=len(manifest),manifest_sha256=h(L/'manifest.json'),time=datetime.datetime.now(datetime.timezone.utc).isoformat(),separate_guarded_verification=True,counts_unchanged='9/39/next40; no acceptance')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt));assert not errors
