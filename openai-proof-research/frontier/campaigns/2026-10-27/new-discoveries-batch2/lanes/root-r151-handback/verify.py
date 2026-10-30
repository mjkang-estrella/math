from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r151'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
counts={}
for name in ['finalmanifest.json','scientific-freeze.json']:
 rows=json.loads((S/name).read_text())['entries']
 for r in rows:assert sha(S/r['path'])==r['sha256'],r['path']
 counts[name]=len(rows)
r=subprocess.run([sys.executable,str(S/'checks.py'),'--verify'],check=True,capture_output=True,text=True)
(P/'replay.log').write_text(r.stdout+r.stderr);j=json.loads(r.stdout)
for name in ['finalmanifest.json','scientific-freeze.json']:
 for row in json.loads((S/name).read_text())['entries']:assert sha(S/row['path'])==row['sha256']
out={'status':'PASS','hash_counts':counts,'read_only_checker_replay':True,'checks':j,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
