import pathlib,json,hashlib,subprocess,sys,datetime
P=pathlib.Path(__file__).resolve().parent
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True)
b=(P/'manifest.json').read_bytes();out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verifier_exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'negative_tests':json.loads((P/'negative-test-results.json').read_text()),'scope':'Integrity only; no math or novelty PASS'}
(P/'final-verification-receipt.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2));sys.exit(r.returncode)
