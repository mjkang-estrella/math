from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parent;L=R.parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
roots=[L/n for n in ['root-mathdb-circulant-review-intake-r381','root-mathdb-circulant-intake-r375','sol-mathdb-circulant-15-certificate-review-r378']]
paths=set(); sets=[]
for root in roots:
 files=sorted(p for p in root.rglob('*') if p.is_file()); paths.update(files)
 m=json.loads((root/'manifest.json').read_text())['files']
 assert {str(p.relative_to(root)) for p in files}-{'manifest.json','verification-receipt.json'}=={e['path'] for e in m}
 for e in m:
  p=root/e['path'];assert p.stat().st_size==e['size'] and sha(p)==e['sha256'],str(p)
 sets.append({'root':str(root),'paths':[str(p.relative_to(root)) for p in files]})
for name,key in [('root-mathdb-circulant-review-intake-r381/bindings.json','copy'),('sol-mathdb-circulant-15-certificate-review-r378/sourcebindings.json','payload')]:
 p=L/name
 for e in json.loads(p.read_text()):
  a=Path(e['original']);b=p.parent/e[key];paths.update([a,b])
  for f in [a,b]:assert sha(f)==e['sha256'] and f.stat().st_size==e['size'],str(f)
(R/'input-freeze.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':[{'path':str(p),'sha256':sha(p),'size':p.stat().st_size} for p in sorted(paths)],'exactsets':sets},indent=2)+'\n')
print('FROZEN',len(paths),'original and retained-copy inputs')
