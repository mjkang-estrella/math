from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r140'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
counts={}
for n in ['finalmanifest.json','scientific-freeze.json']:
 rows=json.loads((S/n).read_text())['files']
 for p,r in rows.items():assert sha(S/p)==r['sha256'],p
 counts[n]=len(rows)
(P/'integrity.json').write_text(json.dumps({'status':'PASS','counts':counts},indent=2)+'\n')
code=(S/'checks.py').read_text().split('# An explicitly finite experimental search;')[0]
(P/'exact-replay.py').write_text(code+"\nreference=json.loads((L.parent/'sol-fresh-source-discovery-r140/checks.json').read_text())\nassert out['exact']==reference['exact']\n(L/'exact-replay.json').write_text(json.dumps(out,indent=2)+'\\n')\nprint('PASS',len(out['exact']),'exact records; floating search deliberately not repeated')\n")
print(counts)
