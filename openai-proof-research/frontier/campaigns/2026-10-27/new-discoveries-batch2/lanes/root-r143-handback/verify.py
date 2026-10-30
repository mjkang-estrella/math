from pathlib import Path
import hashlib,json,shutil
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r143'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
d=json.loads((S/'finalmanifest.json').read_text());rows=d.get('files',d.get('entries',d))
if isinstance(rows,list):rows={r['path']:r for r in rows}
for p,r in rows.items():assert sha(S/p)==(r['sha256'] if isinstance(r,dict) else r),p
Q=P/'replay';Q.mkdir(exist_ok=True)
for n in ['research.py','geometry.py']:shutil.copyfile(S/n,Q/n)
(P/'integrity.json').write_text(json.dumps({'status':'PASS','manifest':len(rows)},indent=2)+'\n');print(len(rows),'verified')
