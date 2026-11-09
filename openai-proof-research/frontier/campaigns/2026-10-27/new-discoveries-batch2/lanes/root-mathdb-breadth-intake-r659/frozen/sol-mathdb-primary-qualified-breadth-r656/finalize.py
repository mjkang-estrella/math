import pathlib,json,hashlib,datetime,subprocess,sys
p=pathlib.Path(__file__).resolve().parent
f=p/'failures.json';a=json.loads(f.read_text());a['helper_failures_preserved']=[{'command':'build.py initial run','exit':1,'reason':'AssertionError: TSV field count; literal vertical bars in ordinal notation collided with delimiter. Replaced notation with ordinal(T) and reran successfully.'}];a['deviations']=['Selected full-page PDF render necessarily includes adjacent unrelated source material above assigned lattice passage; no unrelated MathDB record was selected or reviewed.'];f.write_text(json.dumps(a,indent=2)+'\n')
c=p/'source-coverage.json';a=json.loads(c.read_text());a['visual_inspection']='Bound lattice-passage.png read; printed p2538 confirms statement and remarks. Adjacent top-of-page content incidentally visible, not screened.';c.write_text(json.dumps(a,indent=2)+'\n')
b=p/'flat-bindings.json';a=json.loads(b.read_text())
for path in [p.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py']:
 a[str(path)]={'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'size':path.stat().st_size}
b.write_text(json.dumps(a,indent=2)+'\n')
files=[]
for path in sorted(p.rglob('*')):
 if path.is_file() and path.name not in ['manifest.json','final-verification-receipt.json']:
  files.append({'path':str(path.relative_to(p)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'size':path.stat().st_size})
manifest={'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files}
(p/'manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
r=subprocess.run([sys.executable,'-B',str(p/'verify.py'),'--self-test'],text=True,capture_output=True)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256((p/'manifest.json').read_bytes()).hexdigest(),'manifest_size':(p/'manifest.json').stat().st_size,'verifier_exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'integrity':'PASS' if r.returncode==0 else 'FAIL','mathematical_or_novelty_acceptance':False,'writes':'Only assigned lane; verifier is read-only, negative tests mutate in-memory manifest/file-set views, not originals.'}
(p/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));sys.exit(r.returncode)
