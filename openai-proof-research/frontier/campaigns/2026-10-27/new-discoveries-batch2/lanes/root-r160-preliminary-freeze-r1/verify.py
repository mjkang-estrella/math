from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r160'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
counts={}
for name in ['finalmanifest.json','scientific-freeze.json']:
 rows=json.loads((S/name).read_text())['files']
 for f,h in rows.items():assert sha(S/f)==h,f
 counts[name]=len(rows)
frozen=[{'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(S.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
(P/'review-freeze.json').write_text(json.dumps({'root':str(S),'files':frozen},indent=2)+'\n')
Q=P/'replay';Q.mkdir(exist_ok=True)
for f in ['checks.py','certificate.json']:shutil.copyfile(S/f,Q/f)
r=subprocess.run([sys.executable,str(Q/'checks.py')],capture_output=True,text=True,check=True)
(P/'replay.log').write_text(r.stdout+r.stderr);assert json.loads(r.stdout)==json.loads((S/'checks.json').read_text())
assert (Q/'certificate.json').read_bytes()==(S/'certificate.json').read_bytes()
c=json.loads((Q/'certificate.json').read_text());assert c['minimum_coefficient']==584325
for row in frozen:
 p=Path(row['path']);assert sha(p)==row['sha256'] and p.stat().st_size==row['bytes']
out={'status':'PASS','manifest_counts':counts,'frozen_files':len(frozen),'certificate_byte_identical':True,'coefficient_count':len(c['quotient_coefficients_low_to_high']),'correct_minimum_coefficient':584325,'proof_prose_erratum':'786520 is the constant coefficient, not the minimum','formal_pass':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
