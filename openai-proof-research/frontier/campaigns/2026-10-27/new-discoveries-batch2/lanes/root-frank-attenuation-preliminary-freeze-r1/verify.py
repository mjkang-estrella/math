from pathlib import Path
import hashlib,json,shutil
P=Path(__file__).resolve().parent
S=P.parent/'sol-fresh-source-discovery-r136'
def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for c in iter(lambda:f.read(1048576),b''):h.update(c)
 return h.hexdigest()
counts={}
for name in ['finalmanifest.json','scientific-freeze.json']:
 rows=json.loads((S/name).read_text())['files']
 for r in rows:assert sha(S/r['path'])==r['sha256'],r['path']
 counts[name]=len(rows)
Q=P/'exact-replay';Q.mkdir(exist_ok=True)
for n in ['certify.py','check-results.json']:shutil.copyfile(S/n,Q/n)
rows=[]
for p in sorted(S.rglob('*')):
 if p.is_file() and '__pycache__' not in p.parts:
  rows.append({'path':str(p.relative_to(S)),'bytes':p.stat().st_size,'sha256':sha(p)})
(P/'review-freeze.json').write_text(json.dumps({'source':str(S),'files':rows},indent=2)+'\n')
(P/'integrity.json').write_text(json.dumps({'status':'PASS','counts':counts,'review_paths':len(rows)},indent=2)+'\n')
print(counts,'review paths',len(rows))
