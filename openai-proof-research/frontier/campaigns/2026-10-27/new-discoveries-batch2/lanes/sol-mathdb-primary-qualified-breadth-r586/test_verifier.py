from pathlib import Path
import subprocess,json,sys
D=Path(__file__).resolve().parent;reports=[]
for mode in ['hash','size','extra']:
 p=D/'unexpected-negative-test.tmp'
 if mode=='extra':p.write_text('actual extra file\n')
 try:
  r=subprocess.run([sys.executable,'-B',str(D/'verify.py'),'--negative',mode],capture_output=True,text=True)
  assert r.returncode!=0 and {'hash':'hash mismatch','size':'size mismatch','extra':'exact payload mismatch'}[mode] in r.stderr,(mode,r.stderr)
  reports.append({'test':mode,'exit':r.returncode,'diagnostic':r.stderr.strip(),'rejected':True})
 finally:
  if mode=='extra':p.unlink()
(D/'negative-tests.json').write_text(json.dumps(reports,indent=2)+'\n')
print(json.dumps(reports))
