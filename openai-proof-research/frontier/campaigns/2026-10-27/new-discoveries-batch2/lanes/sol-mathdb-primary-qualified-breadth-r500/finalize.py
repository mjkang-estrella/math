import pathlib,json,hashlib,subprocess,sys,datetime
O=pathlib.Path(__file__).resolve().parent
H=lambda b:hashlib.sha256(b).hexdigest()
def manifest():
 rows=[]
 for p in sorted(O.rglob('*')):
  if p.is_file() and p.relative_to(O).as_posix() not in ['manifest.json','final-receipt.json']:
   b=p.read_bytes();rows.append({'path':p.relative_to(O).as_posix(),'size':len(b),'sha256':H(b)})
 (O/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-receipt.json'],'files':rows},indent=2)+'\n')
manifest()
neg=subprocess.run([sys.executable,str(O/'verify.py'),'--negative-test'],capture_output=True,text=True)
(O/'negative-test.json').write_text(json.dumps({'method':'in-memory deliberate literal corruption in independent verifier','exit_code':neg.returncode,'stdout':neg.stdout,'stderr':neg.stderr,'expected':'nonzero literal mismatch'},indent=2)+'\n')
assert neg.returncode!=0 and 'literal mismatch' in neg.stdout,neg.stdout
manifest()
p=subprocess.run([sys.executable,str(O/'verify.py')],capture_output=True,text=True)
receipt={'verified_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':H((O/'manifest.json').read_bytes()),'verifier_sha256':H((O/'verify.py').read_bytes()),'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'negative_test_rejected':neg.returncode!=0,'limits':'helper_guard.py 512MiB/210CPU/230wall; no bypass','scope':'integrity only; not math or novelty approval'}
(O/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));sys.exit(p.returncode)
