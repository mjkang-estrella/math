from pathlib import Path
import json,tempfile,hashlib
from verify import payload
D=Path(__file__).resolve().parent;out=[]
# Actual small synthetic files, same exact payload validator; never mutate evidence.
for kind in ['hash','size','extra-file']:
 with tempfile.TemporaryDirectory(prefix='negative-',dir=D) as temp:
  p=Path(temp);(p/'test').write_bytes(b'abc')
  entries=[{'path':'test','size':3,'sha256':hashlib.sha256(b'abc').hexdigest()}]
  payload(p,entries,set())
  if kind=='hash':(p/'test').write_bytes(b'abd')
  if kind=='size':(p/'test').write_bytes(b'abcd')
  if kind=='extra-file':(p/'extra').write_bytes(b'')
  try:payload(p,entries,set())
  except AssertionError as e:out.append({'test':kind,'rejected':True,'reason':str(e).replace(str(p),'FIXTURE')})
  else:raise AssertionError('negative accepted: '+kind)
(D/'negative-tests.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
