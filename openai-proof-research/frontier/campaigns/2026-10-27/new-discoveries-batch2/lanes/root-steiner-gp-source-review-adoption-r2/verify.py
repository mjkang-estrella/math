from pathlib import Path
import hashlib,json,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-steiner-gp-source-prior-review-r2'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
def verify():
 rows=json.loads((S/'final-manifest.json').read_text())['files']
 for r in rows:
  p=S/r['path'];assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
 for r in json.loads((S/'before.json').read_text()):
  for k in ['path','copy']:
   p=Path(r[k]);assert sha(p)==r['sha256'] and p.stat().st_size==r['bytes'],str(p)
 return len(rows)
before=verify()
# The supplied verifier only reads evidence and prints a receipt; no lane mutation.
r=subprocess.run([sys.executable,str(S/'verify.py')],capture_output=True,text=True,check=True)
(P/'verifier.log').write_text(r.stdout+r.stderr)
out=json.loads(r.stdout);expected=json.loads((S/'after.json').read_text())
out.pop('utc');expected.pop('utc');assert out==expected
assert verify()==before
files=[]
for p in sorted(S.rglob('*')):
 if p.is_file() and '__pycache__' not in p.parts:files.append({'path':str(p),'bytes':p.stat().st_size,'sha256':sha(p)})
(P/'review-freeze.json').write_text(json.dumps({'files':files},indent=2)+'\n')
receipt={'status':'PASS','review_manifest':before,'original_copy_entries':136,'review_freeze_paths':len(files),'all_receipt_fields_match_except_utc':True,'formal_pass':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
