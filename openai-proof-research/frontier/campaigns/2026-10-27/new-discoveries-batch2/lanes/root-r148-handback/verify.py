from pathlib import Path
import hashlib,json,shutil,subprocess,sys
P=Path(__file__).resolve().parent;S=P.parent/'sol-fresh-source-discovery-r148'
def sha(p):
 with p.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
counts={}
for name in ['finalmanifest.json','scientific-freeze.json']:
 rows=json.loads((S/name).read_text())['entries']
 for r in rows:assert sha(S/r['path'])==r['sha256'],r['path']
 counts[name]=len(rows)
assert sha(S/'sources/public-proof.lean')==sha(S/'sources/public-original.lean')
Q=P/'replay';Q.mkdir(exist_ok=True);shutil.copyfile(S/'checks.py',Q/'checks.py')
r=subprocess.run([sys.executable,str(Q/'checks.py')],check=True,capture_output=True,text=True)
(Q/'checks.json').write_text(r.stdout);assert json.loads(r.stdout)==json.loads((S/'checks.json').read_text())
out={'status':'PASS','hash_counts':counts,'public_proof_original_current_identical':True,'replayed_curvature_coefficients':5,'sign_checks':4,'determinant_controls':5,'byte_identical_output':sha(Q/'checks.json')==sha(S/'checks.json'),'universal_bessel_result':False,'credit':0}
(P/'replay-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
