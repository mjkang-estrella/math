from pathlib import Path
import json,hashlib,datetime,subprocess,sys
O=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[];checks={}
try:
 manifest=json.loads((O/'finalmanifest.json').read_text())
 assert set(manifest['exclusions'])=={'finalmanifest.json','verification-receipt.json'}
 actual={str(p.relative_to(O)) for p in O.rglob('*') if p.is_file() and p.name not in manifest['exclusions']}
 assert actual==set(manifest['files'])
 for p,h in manifest['files'].items():assert sha(O/p)==h,p
 checks['manifest_files']=len(actual)
 for r in json.loads((O/'input-bindings.json').read_text()):
  for key in ['original','frozen','working']:
   p=Path(r[key]) if key=='original' else O/r[key]
   assert sha(p)==r['sha256'],str(p)
 checks['assigned_originals_frozen_working']='PASS'
 for r in map(json.loads,(O/'http.jsonl').read_text().splitlines()):
  assert sha(O/r['path'])==r['sha256']
  assert sha(O/'frozen'/Path(r['path']).name)==r['sha256']
  if r['path'].endswith('.pdf') and r.get('status')==200:
   assert sha(O/'work'/Path(r['path']).name)==r['sha256']
   out=subprocess.run(['pdftotext','-layout',str(O/'work'/Path(r['path']).name),'-'],capture_output=True,check=True)
   assert out.stdout==(O/'work'/(Path(r['path']).stem+'.txt')).read_bytes()
 # Verify the inherited Rossi PDF really extracts to the assigned scientific text.
 out=subprocess.run(['pdftotext','-layout',str(O/'work/1-veto.pdf'),'-'],capture_output=True,check=True)
 assert out.stdout==(O/'work/2-veto.txt').read_bytes()
 checks['http_bodies_and_frozen_copies_and_pdf_extractions']='PASS'
 hs=json.loads((O/'history-screen.json').read_text());assert not hs['failures']
 for r in hs['references']:assert sha(Path(r['path']))==r['sha256']==r['expected']
 checks['historical_references']=len(hs['references'])
 r=subprocess.run([sys.executable,str(O/'scalar_checks.py'),'--verify'],capture_output=True,check=True)
 checks['exact_scalar_cases']=int(r.stdout)
 provenance=json.loads((O/'provenance.json').read_text());assert sha(Path(provenance['guard']['path']))==provenance['guard']['sha256']==sha(O/'guard-copy.py')
 checks['guard_unchanged']='PASS'
 # Recheck after the read-only replay.
 for p,h in manifest['files'].items():assert sha(O/p)==h,p
except Exception as e:errors.append(repr(e))
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pass':not errors,'checks':checks,'errors':errors,'manifest_sha256':sha(O/'finalmanifest.json'),'excluded_receipt':'verification-receipt.json','scope':'integrity/extraction/scalar replay only; not independent mathematical or novelty clearance'}
(O/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2))
sys.exit(bool(errors))
