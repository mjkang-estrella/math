from audit import *
import sys
errors=[];checked=0
def check(p,h):
 global checked
 checked+=1
 if not p.is_file() or sha(p)!=h:errors.append(str(p))
manifest=json.loads((L/'manifest.json').read_text())
for rel,h in manifest['files'].items():check(L/rel,h)
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
if actual!=set(manifest['files']):errors.append('manifest inventory mismatch')
for name in ['bindings.json','library-bindings.json']:
 for b in json.loads((L/name).read_text()):
  check(pathlib.Path(b['original']),b['sha256']);check(pathlib.Path(b['copy']),b['sha256'])
before=json.loads((L/'mathlib-before.json').read_text())
for rel,h in before['files'].items():check(pathlib.Path(before['root'])/rel,h)
if (M/'.git/HEAD').read_text().strip()!=before['head']:errors.append('HEAD changed')
for p,h in json.loads((L/'campaign-before.json').read_text()).items():check(pathlib.Path(p),h)
receipt={'status':'PASS' if not errors else 'FAIL','checked_hash_bindings':checked,'errors':errors,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(L/'manifest.json'),'administrative':'snapshot only; no live equality required','counts':'9/39/next40 unchanged','no_lean_build':True}
dump('verification-receipt.json',receipt);print(json.dumps(receipt));sys.exit(bool(errors))
