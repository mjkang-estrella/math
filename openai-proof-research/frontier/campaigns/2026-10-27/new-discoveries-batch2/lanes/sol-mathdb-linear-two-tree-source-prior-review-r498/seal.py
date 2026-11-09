import pathlib,json,hashlib,datetime
L=pathlib.Path(__file__).resolve().parent
rows=json.loads((L/'initial-bindings.json').read_text())['files']
for pair in json.loads((L/'intake-validation.json').read_text())['direct_original_copy']:rows.append(pair['original'])
for p in [L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parents[4]/'AGENTS.md',L.parent.parent/'AGENTS.md']:
 if p.exists():
  b=p.read_bytes();rows.append({'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
unique={r['path']:r for r in rows}
(L/'flat-original-bindings.json').write_text(json.dumps({'files':list(unique.values()),'note':'References only; no recursive historical/corpus payload copies.'},indent=2)+'\n')
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(L)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(L/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['final-receipt.json','manifest.json'],'files':files},indent=2)+'\n')
print('sealed',len(files),'payloads')
