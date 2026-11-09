import pathlib,json,tempfile,hashlib,subprocess,sys
from verify import exact
D=pathlib.Path(__file__).resolve().parent
out={}
with tempfile.TemporaryDirectory(prefix='negative-fixture-',dir=D) as tmp:
 p=pathlib.Path(tmp);f=p/'fixture.txt';f.write_bytes(b'exact payload\n');b=f.read_bytes()
 entry={'path':'fixture.txt','size':len(b),'sha256':hashlib.sha256(b).hexdigest()};m={'files':[entry],'excluded_exact_paths':[]}
 exact(p,m)
 for kind in ['hash','size','extra_file']:
  bad={'files':[dict(entry)],'excluded_exact_paths':[]}
  if kind=='hash':bad['files'][0]['sha256']='0'*64
  elif kind=='size':bad['files'][0]['size']+=1
  else:(p/'unexpected.txt').write_bytes(b'x')
  # Run rejection in a separate process to demonstrate nonzero exit.
  script='import pathlib,json;from verify import exact;exact(pathlib.Path('+repr(str(p))+'),json.loads('+repr(json.dumps(bad))+'))'
  r=subprocess.run([sys.executable,'-B','-c',script],cwd=D,capture_output=True,text=True)
  assert r.returncode!=0,kind
  out[kind]={'exit':r.returncode,'stderr':r.stderr,'rejected':True}
(D/'negative-test-results.json').write_text(json.dumps(out,indent=2)+'\n')
print('three bounded payload negatives rejected; originals untouched')
