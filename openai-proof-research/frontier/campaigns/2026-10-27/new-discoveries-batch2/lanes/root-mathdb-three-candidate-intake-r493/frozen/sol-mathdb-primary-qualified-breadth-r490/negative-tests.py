from pathlib import Path
import subprocess,sys,json
O=Path(__file__).resolve().parent;G=O.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py';results=[]
for option in ['--negative-literal','--negative-membership']:
 p=subprocess.run([sys.executable,str(G),sys.executable,str(O/'verify.py'),option],capture_output=True,text=True)
 assert p.returncode!=0,(option,'unexpected success')
 results.append(dict(option=option,exit=p.returncode,stdout=p.stdout,stderr=p.stderr,expected='nonzero mismatch failure',status='PASS'))
(O/'negative-tests.json').write_text(json.dumps(results,indent=2)+'\n');print('both bounded negative tests rejected with nonzero exit')
