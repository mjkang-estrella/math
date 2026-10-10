"""Preparation only. Validate, retain all outcomes, then create exactly one seal.
This is NOT the read-only verifier. It refuses to run after sealing.
"""
import pathlib,sys,json,hashlib,subprocess,time,runpy
R=pathlib.Path(__file__).resolve().parents[3];S=R/'frontier/sources/i106_positive_characteristic_imm';X=R/'frontier/experiments/i106_positive_characteristic_imm'
assert not (S/'seal.json').exists(),'Never repair or reseal'
(X/'exact-results.json').write_text(json.dumps(runpy.run_path(str(X/'check_math.py'))['run'](),indent=2)+'\n')
started=time.monotonic()
r=subprocess.run([sys.executable,'-B',str(X/'verify.py'),'--preseal'],cwd=R,capture_output=True,text=True)
event={'command':['python','-B',str((X/'verify.py').relative_to(R)),'--preseal'],'exit_code':r.returncode,'elapsed_seconds':time.monotonic()-started,'stdout':r.stdout,'stderr':r.stderr}
events=json.loads((S/'preseal-events.json').read_text());events.append(event);(S/'preseal-events.json').write_text(json.dumps(events,indent=2)+'\n')
if r.returncode:print(r.stdout,r.stderr);raise SystemExit(r.returncode)
result=json.loads(r.stdout);assert result['status']=='PRESEAL_PASS'
(S/'preseal-validation.json').write_text(json.dumps(result,indent=2)+'\n')
# The verifier has validated substantive contents. Newly written records retain its
# exact outcome and are included, together with this script, in the single seal.
paths=[R/'frontier/iterations/i106-positive-characteristic-imm.md']
for base in [S,X]:
 for p in base.rglob('*'):
  assert not p.is_symlink()
  if p.is_file():paths.append(p)
seal={'schema':'i106-integrity-seal-v1','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','policy':'One final seal after successful validation. No postseal edits or resealing. Seal itself is the excluded root manifest.','scope':'Evidence integrity and exact finite diagnostics; not proof or substantiality certification','original_i103_seal_sha256':'b3eaa8ec05a4bb443476b61d2af487ee73fb2393b992fef3ccfb572a8b59949f','files':{str(p.relative_to(R)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}}
with (S/'seal.json').open('x') as f:f.write(json.dumps(seal,indent=2)+'\n')
print(json.dumps({'status':'SEALED_AFTER_PRESEAL_PASS','sealed_files':len(paths),'seal_sha256':hashlib.sha256((S/'seal.json').read_bytes()).hexdigest()}))
