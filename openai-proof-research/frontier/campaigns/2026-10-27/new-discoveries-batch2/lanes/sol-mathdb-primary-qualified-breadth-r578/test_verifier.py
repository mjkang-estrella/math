from pathlib import Path
import tempfile,json,hashlib
from verify import payload
D=Path(__file__).resolve().parent
results=[]
# Only tiny synthetic scratch files in assigned lane; no originals modified/copied.
with tempfile.TemporaryDirectory(dir=D,prefix='negative-scratch-') as td:
 p=Path(td);f=p/'x';f.write_bytes(b'abc')
 m={'files':[{'path':'x','size':3,'sha256':hashlib.sha256(b'abc').hexdigest()}],'excluded_exact_paths':['manifest.json','final-verification-receipt.json']}
 payload(p,m)
 for name,change in [('hash',lambda:f.write_bytes(b'abd')),('size',lambda:f.write_bytes(b'abcd')),('extra-file',lambda:(p/'extra').write_bytes(b'x'))]:
  f.write_bytes(b'abc')
  if (p/'extra').exists():(p/'extra').unlink()
  change()
  try:payload(p,m);raise RuntimeError('negative accepted: '+name)
  except AssertionError as e:results.append({'mutation':name,'rejected':True,'error':str(e)})
(D/'negative-tests.json').write_text(json.dumps({'control':'PASS','tests':results,'originals_mutated':False},indent=2)+'\n');print(results)
