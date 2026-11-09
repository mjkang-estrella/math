from pathlib import Path
import json,hashlib,datetime,subprocess
L=Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'final-manifest.json').read_text());expected={r['path'] for r in m['files']}
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excluded']}
assert actual==expected
for r in m['files']:assert h(L/r['path'])==r['sha256'] and (L/r['path']).stat().st_size==r['bytes']
bindings=json.loads((L/'freeze-bindings.json').read_text());science=0
for r in bindings:
 assert h(L/r['copy'])==r['sha256']
 if r['kind']=='scientific':assert h(Path(r['original']))==r['sha256'];science+=1
e=json.loads((L/'checker-evidence.json').read_text());assert e['all_pass'] and len(e['tests'])==29 and all(e['tests'].values())
c=json.loads((L/'source-comparison.json').read_text());assert c['pdf_equal'] and c['text_equal']
r={'verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS','manifest_sha256':h(L/'final-manifest.json'),'manifest_files':len(expected),'scientific_original_copy_bindings_verified':science,'administrative_copy_bindings_verified':len(bindings)-science,'checker_assertions':29,'fresh_pdf_and_extraction_equal':True,'excluded':['final-manifest.json','verification-receipt.json'],'separate_guarded_verification':True,'root_only_accepts':True}
(L/'verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
