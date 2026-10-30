from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r169'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for name,count in [('scientific-freeze.json',81),('finalmanifest.json',82)]:
 rows=json.loads((S/name).read_text())['entries'];assert len(rows)==count
 for r in rows:
  p=S/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
assert {r['path'] for r in rows}=={str(p.relative_to(S)) for p in S.rglob('*') if p.is_file() and p.name not in {'finalmanifest.json','manifest-verification.json'}}
for r in json.loads((S/'inherited-evidence.json').read_text())['records']:assert sha(Path(r['original']))==r['sha256']
D=P/'own-checks';D.mkdir(exist_ok=True)
for script,result in [('checks.py','checks.json'),('route_checks.py','route-checks.json')]:
 shutil.copyfile(S/script,D/script)
 with (D/(script+'.log')).open('w') as f:subprocess.run([sys.executable,str(D/script)],check=True,stdout=f,stderr=subprocess.STDOUT)
 assert (D/result).read_bytes()==(S/result).read_bytes(),result
files=[{'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(S.rglob('*')) if p.is_file()]
(P/'review-freeze.json').write_text(json.dumps({'files':files},indent=2)+'\n')
out={'status':'PASS','manifest_entries':82,'scientific_entries':81,'frozen_files':len(files),'both_checker_outputs_byte_identical':True,'credit':0,'eligibility':'HOLD'}
(P/'verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
