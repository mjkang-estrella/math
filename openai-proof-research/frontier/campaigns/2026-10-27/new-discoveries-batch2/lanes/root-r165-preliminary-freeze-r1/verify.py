from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r165'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify():
 counts={}
 for name in ['finalmanifest.json','scientific-freeze.json']:
  rows=json.loads((S/name).read_text())['entries']
  for r in rows:
   p=S/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
  counts[name]=len(rows)
 return counts
before=verify();Q=P/'replay';Q.mkdir(exist_ok=True)
for f in ['checks.py','amplification.py']:shutil.copyfile(S/f,Q/f)
for f in ['checks.py','amplification.py']:
 r=subprocess.run([sys.executable,str(Q/f)],capture_output=True,text=True,check=True)
 (P/(f+'.log')).write_text(r.stdout+r.stderr)
for f in ['checks.json','amplification.json']:assert (Q/f).read_bytes()==(S/f).read_bytes(),f
b=json.loads((Q/'amplification.json').read_text());after=verify();assert before==after
files=[]
for p in sorted(S.rglob('*')):
 if p.is_file() and '__pycache__' not in p.parts:files.append({'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)})
(P/'review-freeze.json').write_text(json.dumps({'root':str(S),'files':files},indent=2)+'\n')
out={'status':'PASS','before':before,'after':after,'byte_identical_checks':True,'freeze_paths':len(files),'vertices':b['n'],'gp_lower':b['gp_lower'],'sgp3_upper':b['sgp3_upper'],'gp_triples':b['gp_triples'],'rim_triples':b['rim_triples'],'formal_pass':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
