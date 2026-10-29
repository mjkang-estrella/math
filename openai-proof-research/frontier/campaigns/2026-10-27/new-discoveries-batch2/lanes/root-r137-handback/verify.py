from pathlib import Path
import hashlib,json,shutil
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r137'
def sha(p):return hashlib.file_digest(p.open('rb'),'sha256').hexdigest()
counts={}
for name in ['finalmanifest.json','scientific-freeze.json']:
 rows=json.loads((S/name).read_text())['files']
 for p,h in rows.items():assert sha(S/p)==h,p
 counts[name]=len(rows)
Q=P/'replay';Q.mkdir(exist_ok=True);shutil.copyfile(S/'checks.py',Q/'checks.py')
(P/'integrity.json').write_text(json.dumps({'status':'PASS','counts':counts},indent=2)+'\n')
print(counts)
