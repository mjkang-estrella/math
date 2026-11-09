from pathlib import Path
import json,hashlib,subprocess,sys,datetime
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'MANIFEST.json').read_text())
def verify():
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['MANIFEST.json','verification-receipt.json']}
 assert actual==set(m)
 for name,digest in m.items():assert h(L/name)==digest,name
 for r in json.loads((L/'source-bindings.json').read_text()):
  assert h(L/r['copy'])==r['sha256']
  if 'original' in r:assert h(Path(r['original']))==r['sha256']
verify()
subprocess.run([sys.executable,str(L/'check.py')],check=True)
verify()
receipt={'PASS':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':h(L/'MANIFEST.json'),'files_verified':len(m),'original_copy_bindings_verified':True,'independent_checker_rerun':True,'manifest_rechecked_after_rerun':True,'acceptance_or_credit':False}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
