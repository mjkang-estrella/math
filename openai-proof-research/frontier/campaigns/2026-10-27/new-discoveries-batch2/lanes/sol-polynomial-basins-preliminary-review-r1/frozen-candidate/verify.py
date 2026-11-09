import pathlib,json,hashlib,datetime,os
L=pathlib.Path(__file__).parent
def h(p):return hashlib.sha256(p.read_bytes()).hexdigest()
manifest=json.loads((L/'final-manifest.json').read_text());errors=[]
assert 'final-manifest.json' not in manifest and 'verification-receipt.json' not in manifest
actual={str(p.relative_to(L)) for p in L.rglob('*') if p.is_file() and p.name not in {'final-manifest.json','verification-receipt.json'}}
if actual!=set(manifest):errors.append('file inventory mismatch')
for name,entry in manifest.items():
 p=L/name
 if not p.is_file() or h(p)!=entry['sha256'] or p.stat().st_size!=entry['bytes']:errors.append('manifest mismatch '+name)
bindings=json.loads((L/'source-bindings.json').read_text())
for r in bindings:
 for key in ['original','copy']:
  if h(pathlib.Path(r[key]))!=r['sha256']:errors.append('scientific binding mismatch '+r[key])
for old,new in [('iterations.pdf','original-borisov.pdf'),('dismal.pdf','original-dismal.pdf')]:
 cached=L.parent/'sol-decimal-pairs-breadth-depth-r234/sources'/old
 if h(cached)!=h(L/'sources'/new):errors.append('live/cache mismatch '+old)
assert json.loads((L/'exact-checks.json').read_text())['status']=='PASS'
ledger=json.loads((L/'admin/ledger.json').read_text());assert [ledger[k] for k in ['accepted_count','total_accepted_count','next_global_outcome_number']]==[9,39,40]
required=['SUMMARY.md','SCOUTING.md','discovery.md','progress.md','provenance.json','PROOF.md','routine-proof.md','FAILURES.md']
assert all(x in manifest for x in required)
receipt=dict(status='PASS' if not errors else 'FAIL',timestamp=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=h(L/'final-manifest.json'),manifest_files=len(manifest),scientific_bindings_verified=len(bindings),live_cached_primary_equality=True,diagnostics='PASS',errors=errors,counts=[9,39,40],verification='separate guarded invocation after all final writes; integrity only, not independent mathematical review',environment={k:os.environ.get(k) for k in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','PYTHONDONTWRITEBYTECODE']},resource_caps='external immutable helper_guard: AS/groupRSS512MiB CPU210 wall230; no raises')
(L/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2));assert not errors
