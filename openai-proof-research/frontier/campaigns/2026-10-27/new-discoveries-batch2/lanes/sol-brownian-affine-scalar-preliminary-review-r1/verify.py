from pathlib import Path
import json,hashlib,datetime
p=Path(__file__).resolve().parent
def sha(q):return hashlib.sha256(q.read_bytes()).hexdigest()
manifest=json.loads((p/'finalmanifest.json').read_text());bad=[]
assert manifest['explicit_exclusions']==['finalmanifest.json','manifest-verification.json']
listed={r['path'] for r in manifest['files']}
actual={str(q.relative_to(p)) for q in p.rglob('*') if q.is_file()}-set(manifest['explicit_exclusions'])
if listed!=actual:bad.append({'file_set_difference':sorted(listed^actual)})
for r in manifest['files']:
 q=p/r['path']
 if sha(q)!=r['sha256'] or q.stat().st_size!=r['bytes']:bad.append(r['path'])
f=json.loads((p/'freeze-before.json').read_text())
for r in f['inputs']:
 if sha(Path(r['original']))!=r['sha256'] or sha(p/r['copy'])!=r['sha256']:bad.append(r['original'])
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'status':'FAIL' if bad else 'PASS','manifest_sha256':sha(p/'finalmanifest.json'),
 'manifest_files':len(listed),'original_copy_pairs':len(f['inputs']),
 'explicit_exclusions':manifest['explicit_exclusions'],'failures':bad,
 'limits':'Separate guarded execution after final writes. Integrity verification only; no proof or novelty certification.'}
(p/'manifest-verification.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt));assert not bad
