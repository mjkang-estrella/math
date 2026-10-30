from pathlib import Path
import sys,json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(n,j):(L/n).write_text(json.dumps(j,indent=2)+'\n')
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
mode=sys.argv[1]
if mode=='science':
 rows=json.loads((L/'scientific-input-freeze.json').read_text())['bindings'];errors=[]
 for p,c,h,z in rows:
  for q in [Path(p),L/c]:
   if not q.is_file() or sha(q)!=h or q.stat().st_size!=z:errors.append(str(q))
 science=json.loads((L/'scientific-freeze.json').read_text())['files']
 for p,h,z in science:
  if sha(L/p)!=h or (L/p).stat().st_size!=z:errors.append(p)
 g=json.loads((L/'guard-binding.json').read_text());assert sha(Path(g['path']))==g['sha256']
 save('scientific-verification.json',dict(utc=utc(),original_copy_pairs=len(rows),lane_scientific_files=len(science),errors=errors,pass_all=not errors,administrative_policy='Live NEXT/ledger/prior context not checked; frozen administrative snapshots are manifest-covered'))
 print('science',len(rows),len(science),'errors',errors);assert not errors
elif mode=='manifest':
 exclusions=['finalmanifest.json','manifest-verification.json']
 rows=[[str(p.relative_to(L)),sha(p),p.stat().st_size] for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in exclusions]
 save('finalmanifest.json',dict(utc=utc(),explicit_exclusions=exclusions,reason='Manifest cannot bind its own hash; separate verification receipt written after manifest is explicitly excluded',files=rows));print('manifest',len(rows))
elif mode=='final':
 manifest=L/'finalmanifest.json';j=json.loads(manifest.read_text());errors=[]
 for p,h,z in j['files']:
  if not (L/p).is_file() or sha(L/p)!=h or (L/p).stat().st_size!=z:errors.append(p)
 actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-set(j['explicit_exclusions'])
 assert actual=={p for p,h,z in j['files']}
 # Recheck scientific originals/copies after ALL scientific/final writes.
 rows=json.loads((L/'scientific-input-freeze.json').read_text())['bindings']
 for p,c,h,z in rows:
  for q in [Path(p),L/c]:
   if not q.is_file() or sha(q)!=h or q.stat().st_size!=z:errors.append(str(q))
 save('manifest-verification.json',dict(utc=utc(),manifest_sha256=sha(manifest),manifest_files=len(j['files']),original_copy_pairs=len(rows),explicit_exclusions=j['explicit_exclusions'],errors=errors,pass_all=not errors,separate_guarded_invocation=True))
 print('final',len(j['files']),len(rows),'errors',errors);assert not errors
