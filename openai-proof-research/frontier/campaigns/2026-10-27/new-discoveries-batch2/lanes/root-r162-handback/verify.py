from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r162'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify():
 counts={}
 for name in ['finalmanifest.json','scientific-freeze.json']:
  rows=json.loads((S/name).read_text())['entries']
  for path,r in rows.items():
   p=S/path;assert sha(p)==(r if isinstance(r,str) else r['sha256']),str(p)
   if isinstance(r,dict):assert p.stat().st_size==r['bytes']
  counts[name]=len(rows)
 return counts
before=verify();Q=P/'replay';Q.mkdir(exist_ok=True)
for f in ['checks.py','triangle.py','controls.py']:shutil.copyfile(S/f,Q/f)
for f in ['checks.py','triangle.py','controls.py']:
 r=subprocess.run([sys.executable,str(Q/f)],capture_output=True,text=True,check=True)
 (P/(f+'.log')).write_text(r.stdout+r.stderr)
outputs=['checks.json','triangle-checks.json','controls.json']
for f in outputs:assert (Q/f).read_bytes()==(S/f).read_bytes(),f
b=json.loads((Q/'checks.json').read_text());c=json.loads((Q/'controls.json').read_text())
after=verify();assert before==after
out={'status':'PASS','before':before,'after':after,'byte_identical_outputs':outputs,'small_connected_graphs':sum(x['connected_labeled'] for x in b['small']),'efficient_cubic':len(b['efficient_cubic']),'triangle_controls':len(c['triangle']),'public_stirling_vector':c['public_stirling_vector'],'universal_result':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
