from pathlib import Path
import hashlib,json,datetime
l=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
errors=[];checked=0
for name in ['bindings.json','primarybindings.json','reopened-bindings.json','retrieval-bindings.json']:
 for r in json.loads((l/name).read_text()):
  if 'error' in r:continue
  for key in ['original','copy']:
   checked+=1
   if sha(r[key])!=r['sha256']:errors.append({'binding':name,'path':r[key]})
history_checked=0
for name in ['history-bindings.json','expanded-history-bindings.json']:
 for r in json.loads((l/name).read_text()):
  history_checked+=1
  if sha(r['path'])!=r['sha256']:errors.append({'immutable_history_drift':r['path'],'binding':name})
manifest=json.loads((l/'finalmanifest.json').read_text())
for p,h in manifest.items():
 checked+=1
 if sha(l/p)!=h:errors.append({'manifest':p})
actual={str(p.relative_to(l)) for p in l.rglob('*') if p.is_file() and p.name not in ['finalmanifest.json','verification-receipt.json']}
if actual!=set(manifest):errors.append({'manifest_inventory_mismatch':sorted(actual.symmetric_difference(manifest))})
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS' if not errors else 'FAIL','scientific_and_manifest_checks':checked,'immutable_history_checks':history_checked,'administrative_originals':'not compared; snapshots only','errors':errors,'meaning':'integrity only, not proof/novelty/substantive acceptance'}
(l/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt));raise SystemExit(bool(errors))
