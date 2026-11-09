import pathlib,json,hashlib,subprocess,datetime,os
P=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  b=p.read_bytes();files.append(dict(path=str(p.relative_to(P)),sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
(P/'manifest.json').write_text(json.dumps(dict(excluded_exact_paths=['manifest.json','final-verification-receipt.json'],files=files),indent=2,sort_keys=True)+'\n')
r=subprocess.run(['python3','-B',str(P/'verify.py'),'--negative-tests'],capture_output=True,text=True)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verifier_exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'manifest_sha256':hashlib.sha256((P/'manifest.json').read_bytes()).hexdigest(),'manifest_size':(P/'manifest.json').stat().st_size,'execution':'Within unchanged fixed guard:512MiB AS/groupRSS CPU210s wall230s; python3 -B and prescribed thread environment. No upstream verifier execution.','negative_test_limit':'In-memory mutations exercise same byte/size/exact-name validators; no original or source payload mutation.'}
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print(json.dumps(receipt));assert r.returncode==0
