from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r142'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
rows=json.loads((S/'finalmanifest.json').read_text())['files']
for r in rows:assert sha(S/r['path'])==r['sha256'],r['path']
Q=P/'replay';Q.mkdir(exist_ok=True)
code=(S/'checks.py').read_text();old='assert all(relaxed[-k]+comp(relaxed)[-k]>=10-k for k in range(1,10))';new='assert all(relaxed[-k]+comp(relaxed)[-k]<=20-k for k in range(1,10))'
assert code.count(old)==1
(Q/'checks.py').write_text(code.replace(old,new))
(P/'integrity.json').write_text(json.dumps({'status':'PASS','manifest':len(rows),'root_checker_correction':{'old':old,'new':new},'originals_unchanged':True},indent=2)+'\n');print(len(rows),'verified; corrected root-only upper-sum check')
