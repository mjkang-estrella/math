from pathlib import Path
import hashlib,json,shutil
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r139'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
counts={}
for n in ['finalmanifest.json','scientific-freeze.json']:
 d=json.loads((S/n).read_text());rows=d.get('entries',d.get('files',d))
 for p,r in rows.items():assert sha(S/p)==(r['sha256'] if isinstance(r,dict) else r),p
 counts[n]=len(rows)
Q=P/'replay';Q.mkdir(exist_ok=True);shutil.copyfile(S/'checks.py',Q/'checks.py')
(P/'integrity.json').write_text(json.dumps({'status':'PASS','counts':counts},indent=2)+'\n');print(counts)
