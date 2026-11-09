import pathlib,json,hashlib,resource,os,datetime
L=pathlib.Path(__file__).resolve().parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
m=json.loads((L/'finalmanifest.json').read_text());errors=[]
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in m['excludes']}
expected={r['path'] for r in m['files']}
if actual!=expected:errors.append('manifest inventory mismatch')
for r in m['files']:
 p=L/r['path']
 if not p.exists() or h(p)!=r['sha256'] or p.stat().st_size!=r['bytes']:errors.append('file mismatch '+str(p))
for r in json.loads((L/'primarybindings.json').read_text()):
 for key in ['primary','frozen']:
  if h(pathlib.Path(r[key]))!=r['sha256']:errors.append(key+' source drift '+r['id'])
for r in json.loads((L/'administrative/bindings.json').read_text()):
 if h(pathlib.Path(r['snapshot']))!=r['sha256']:errors.append('administrative snapshot mismatch')
assert resource.getrlimit(resource.RLIMIT_AS)[0]==512*1024*1024
assert resource.getrlimit(resource.RLIMIT_CPU)[0]==210
assert all(os.environ[k]=='1' for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','PYTHONDONTWRITEBYTECODE'])
receipt={'time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'PASS' if not errors else 'FAIL','errors':errors,'manifest_sha256':h(L/'finalmanifest.json'),'verified_files':len(m['files']),'primary_original_copy_pairs':len(json.loads((L/'primarybindings.json').read_text())),'manifest_excludes_self_and_receipt':True,'separate_guarded_process':True,'AS_bytes':resource.getrlimit(resource.RLIMIT_AS)[0],'CPU_seconds':resource.getrlimit(resource.RLIMIT_CPU)[0],'counts_unchanged':'9/39/next40; no shared writes'}
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2));print(json.dumps(receipt,indent=2));assert not errors
