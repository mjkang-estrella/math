import pathlib,json,hashlib,subprocess,sys,datetime
P=pathlib.Path(__file__).resolve().parent
subprocess.run([sys.executable,'-B',str(P/'seal.py')],check=True)
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True)
b=(P/'manifest.json').read_bytes();o={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verifier_exit':r.returncode,'verifier_stdout':r.stdout.strip(),'verifier_stderr':r.stderr.strip(),'negative_tests':json.loads((P/'negative-test-results.json').read_text()),'scope':'Administrative integrity only; math/source-dependency/current-registry/novelty clearance not granted.','helper_guard':'fixed 512MiB AS and groupRSS, CPU210s wall230s; no changes','payload_file_count':len(json.loads(b)['files'])}
(P/'final-verification-receipt.json').write_text(json.dumps(o,indent=2)+'\n');print(json.dumps(o,indent=2));sys.exit(r.returncode)
