from pathlib import Path
import hashlib,json,shutil
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r141'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
d=json.loads((S/'finalmanifest.json').read_text());rows=d['files']
for r in rows:assert sha(S/r['path'])==r['sha256'],r['path']
Q=P/'replay';Q.mkdir(exist_ok=True);shutil.copyfile(S/'checks.py',Q/'checks.py')
(P/'integrity.json').write_text(json.dumps({'status':'PASS','manifest':len(rows)},indent=2)+'\n');print(len(rows),'verified')
