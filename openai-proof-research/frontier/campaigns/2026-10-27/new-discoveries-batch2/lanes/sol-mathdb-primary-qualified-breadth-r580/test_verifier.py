from pathlib import Path
import json,tempfile,hashlib,copy
from verify import payload
D=Path(__file__).parent;out=[]
with tempfile.TemporaryDirectory(dir=D) as t:
 p=Path(t);(p/'x').write_bytes(b'original');m={'files':[dict(path='x',size=8,sha256=hashlib.sha256(b'original').hexdigest())]};payload(p,m)
 for kind in ['hash','size','extra-file']:
  z=copy.deepcopy(m)
  if kind=='hash':z['files'][0]['sha256']='0'*64
  if kind=='size':z['files'][0]['size']=9
  if kind=='extra-file':(p/'extra').write_bytes(b'x')
  rejected=False
  try:payload(p,z)
  except AssertionError:rejected=True
  assert rejected;out.append(dict(test=kind,rejected=True,originals_mutated=False))
(D/'negative-tests.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
