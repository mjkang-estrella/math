from pathlib import Path
import json,subprocess,sys,tempfile,shutil
O=Path(__file__).resolve().parent;out=[]
for kind in ['hash','size','extra-file']:
 with tempfile.TemporaryDirectory(prefix='negative-',dir=O) as td:
  T=Path(td);p=T/'fixture';p.mkdir()
  for e in json.loads((O/'manifest.json').read_text())['files']:
   dest=p/e['path'];dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(O/e['path'],dest)
  shutil.copyfile(O/'manifest.json',p/'manifest.json')
  target=p/'proposals.json'
  if kind=='hash':target.write_bytes(b'[ ]') # same three-byte size; different digest
  if kind=='size':target.write_bytes(target.read_bytes()+b' ')
  if kind=='extra-file':(p/'UNEXPECTED').write_text('negative fixture only')
  r=subprocess.run([sys.executable,'-B',str(O/'verify.py'),'--payload-root',str(p)],capture_output=True,text=True)
  assert r.returncode!=0
  expected={'hash':'hash mismatch','size':'size mismatch','extra-file':'extra or missing payload file'}[kind];assert expected in r.stderr
  out.append(dict(test=kind,rejected=True,exit=r.returncode,stderr=r.stderr.strip()))
(O/'negative-tests.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
