import pathlib,hashlib,json,datetime,subprocess,sys,resource
L=pathlib.Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
errors=[]
manifest=json.loads((L/'manifest.json').read_text())
for n,h in manifest.items():
 if sha(L/n)!=h:errors.append('manifest '+n)
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']}
if actual!=set(manifest):errors.append('manifest coverage')
for r in json.loads((L/'freeze.json').read_text())['refs']:
 if sha(r['copy'])!=r['sha256']:errors.append('frozen copy '+r['original'])
current={r['path']:r for r in json.loads((L/'original-recheck.json').read_text())}
for file in ['history-freeze.json','all-text-bindings.json','original-recheck.json']:
 for r in json.loads((L/file).read_text()):
  expected=current.get(r['path'],r)['sha256']
  if sha(r['path'])!=expected:errors.append('binding '+r['path'])
for line in (L/'sourcebytes.jsonl').read_text().splitlines():
 r=json.loads(line)
 if sha(r['path'])!=r['sha256']:errors.append('primary '+r['path'])
p=subprocess.run([sys.executable,str(L/'checks.py')],capture_output=True,text=True)
if p.returncode:errors.append('exact checks '+p.stderr)
# Deterministic regeneration must preserve the final manifested bytes.
if sha(L/'checks.json')!=manifest['checks.json']:errors.append('check output nondeterminism')
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pass':not errors,'errors':errors,'acknowledged_active_original_changes':[r for r in current.values() if r['changed']],'manifest_sha256':sha(L/'manifest.json'),'manifest_files':len(manifest),'checks_exit':p.returncode,'guard':'specified external helper_guard.py; fixed AS/groupRSS512MiB CPU210 wall230','RLIMIT_AS':resource.getrlimit(resource.RLIMIT_AS),'RLIMIT_CPU':resource.getrlimit(resource.RLIMIT_CPU),'scope':'file integrity and finite exact identities, NOT novelty or universal wavelet proof'}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2));sys.exit(bool(errors))
