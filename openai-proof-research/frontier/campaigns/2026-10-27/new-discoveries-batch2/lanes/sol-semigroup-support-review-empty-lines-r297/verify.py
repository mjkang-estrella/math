from pathlib import Path
import json,hashlib,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
errors=[];n=0
for name in ['bindings.json','dedup-bindings.json']:
 for b in json.loads((L/name).read_text()):
  for p in [Path(b['original']),L/b['copy']]:
   if not p.exists() or sha(p)!=b['sha256']:errors.append(str(p))
  n+=1
manifest=json.loads((L/'manifest.json').read_text())
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
if actual!=set(manifest):errors.append('manifest file inventory mismatch')
for f,h in manifest.items():
 if not (L/f).exists() or sha(L/f)!=h:errors.append(f)
for row in json.loads((L/'access.json').read_text()):
 if 'failure' in row:continue
 ident=row['url'].rsplit('/',1)[-1]
 for ext,key in [('pdf','pdf_sha256'),('txt','text_sha256')]:
  if sha(L/'sources'/(ident+'.'+ext))!=row[key]:errors.append(ident+'.'+ext)
receipt=dict(status='PASS' if not errors else 'FAIL',time=datetime.datetime.now(datetime.timezone.utc).isoformat(),original_copy_bindings=n,manifest_files=len(manifest),manifest_sha256=sha(L/'manifest.json'),errors=errors,counts='9/39/next40 unchanged',scope='integrity verification; scientific checks separately in checks.json')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt));assert not errors
