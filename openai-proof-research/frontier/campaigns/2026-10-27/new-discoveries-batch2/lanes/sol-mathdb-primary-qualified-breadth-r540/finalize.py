import pathlib,json,hashlib,subprocess,sys,datetime
P=pathlib.Path(__file__).resolve().parent
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True)
assert r.returncode==0,r.stderr
b=(P/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','manifest':{'path':'manifest.json','sha256':hashlib.sha256(b).hexdigest(),'size':len(b)},'verification':json.loads(r.stdout),'negative_tests':json.loads((P/'negative-test-results.json').read_text()),'originals_verified':True,'intake_verifier_executed':False,'math_acceptance':False,'novelty_clearance':False,'credit':0,'new_literal_reviews':50,'root_reconciliation_pending':True}
(P/'verification-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print(json.dumps(receipt['manifest']))
