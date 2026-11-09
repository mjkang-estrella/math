import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent
f=P/'flat-bindings.json';refs=json.loads(f.read_text());guard=P.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py';b=guard.read_bytes()
if not any(e['path']==str(guard) for e in refs):refs.append({'path':str(guard),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
f.write_text(json.dumps(refs,indent=2)+'\n')
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files},indent=2)+'\n')
