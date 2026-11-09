from pathlib import Path
import hashlib,json,datetime
p=Path(__file__).resolve().parent.parent
h=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
manifest=json.loads((p/'finalmanifest.json').read_text())
errors=[]
for r in manifest['files']:
 if h(p/r['path'])!=r['sha256']:errors.append('manifest:'+r['path'])
for r in json.loads((p/'inputs/freeze.json').read_text()):
 for key in ['original','copy']:
  if h(Path(r[key]))!=r['sha256']:errors.append('input:'+r[key])
for r in json.loads((p/'source-bindings.json').read_text())['records']:
 for key in ['original','copy']:
  if h(Path(r[key]))!=r['sha256']:errors.append('source:'+r[key])
for r in json.loads((p/'history-original-verification.json').read_text())['records']:
 if h(Path(r['snapshot']))!=r['sha256']:errors.append('history snapshot:'+r['snapshot'])
 if r['original_matches'] and h(Path(r['original']))!=r['sha256']:errors.append('history original changed:'+r['original'])
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h(p/'finalmanifest.json'),'manifest_files':len(manifest['files']),'frozen_input_pairs':len(json.loads((p/'inputs/freeze.json').read_text())),'source_pairs':len(json.loads((p/'source-bindings.json').read_text())['records']),'immutable_history_references':len(json.loads((p/'history-bindings.json').read_text())),'errors':errors,'pass':not errors,'exclusions':['finalmanifest.json','verification-receipt.json'],'scope':'Separate guarded verification after final report and manifest writes. Admin files are snapshots only; not live scientific bindings.'}
(p/'verification-receipt.json').write_text(json.dumps(receipt,indent=2))
print(json.dumps(receipt,indent=2))
assert not errors
