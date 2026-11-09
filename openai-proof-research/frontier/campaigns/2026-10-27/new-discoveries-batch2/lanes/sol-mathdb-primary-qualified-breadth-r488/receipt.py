from pathlib import Path
import subprocess,json,datetime,os
O=Path(__file__).parent;guard=O.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py';results=[]
for args in [[],['--negative-test']]:
 r=subprocess.run(['python',str(guard),'python',str(O/'verify.py')]+args,capture_output=True,text=True,env=os.environ)
 results.append({'args':args,'exit_code':r.returncode,'stdout':r.stdout,'guard_stderr':r.stderr})
ok=results[0]['exit_code']==0 and results[1]['exit_code']==1 and 'literal statement mismatch' in results[1]['stdout']
receipt={'status':'PASS' if ok else 'FAIL','executed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'verification_runs':results,'negative_test_expected_nonzero':True,'mathematical_or_novelty_pass':False,'scope_deviation_disclosed_in':'failures.json'}
(O/'verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));raise SystemExit(0 if ok else 1)
