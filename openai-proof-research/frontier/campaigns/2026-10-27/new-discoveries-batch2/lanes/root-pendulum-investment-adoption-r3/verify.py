from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;S=P.parent/'sol-pendulum-investment-review-r3'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
rows=json.loads((S/'final-verified-manifest.json').read_text())['files']
for r in rows:
 p=S/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
total=0
for name in ['freeze-0.json','freeze-1.json']:
 for r in json.loads((S/name).read_text())['files']:
  p=Path(r['path']);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p);total+=1
assert total==308
files=[{'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(S.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
(P/'review-freeze.json').write_text(json.dumps({'files':files},indent=2)+'\n')
out={'status':'PASS','manifest_entries':len(rows),'frozen_originals':total,'review_freeze_paths':len(files),'formal_pass':False,'credit':0}
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
