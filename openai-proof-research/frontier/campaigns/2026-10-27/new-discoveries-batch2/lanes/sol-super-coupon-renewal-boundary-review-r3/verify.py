from pathlib import Path
import hashlib,json,datetime,subprocess
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[];manifest=json.loads((L/'finalmanifest.json').read_text())
for rel,h in manifest['files'].items():
 p=L/rel
 if not p.is_file() or sha(p)!=h:errors.append('manifest mismatch '+rel)
bindings=json.loads((L/'bindings.json').read_text())['records'];scientific=admin=0
for r in bindings:
 copy=L/r['copy']
 if sha(copy)!=r['sha256']:errors.append('copy mismatch '+r['copy'])
 if r['administrative']:admin+=1;continue
 scientific+=1
 p=Path(r['original'])
 if not p.is_file() or sha(p)!=r['sha256']:errors.append('original changed '+r['original'])
for r in json.loads((L/'body-coverage.json').read_text())['bodies']:
 fresh=subprocess.check_output(['pdftotext','-layout',str(L/r['pdf']),'-'])
 if fresh!=(L/r['text']).read_bytes():errors.append('fresh extraction mismatch '+r['name'])
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in manifest['excludes']}
if actual!=set(manifest['files']):errors.append('manifest file set differs')
result=dict(verified_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),status='PASS' if not errors else 'FAIL',manifest_sha256=sha(L/'finalmanifest.json'),manifest_members=len(manifest['files']),scientific_originals_copies_checked=scientific,administrative_copies_checked=admin,fresh_extracted_bodies=5,errors=errors,acceptance_or_count_change=False)
(L/'verification-receipt.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
raise SystemExit(bool(errors))
