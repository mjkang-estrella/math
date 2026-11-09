import pathlib,json,hashlib,datetime,subprocess,sys,tempfile,shutil
D=pathlib.Path(__file__).resolve().parent
EX=['manifest.json','final-verification-receipt.json']
def manifest():
 files=[]
 for p in sorted(D.rglob('*')):
  if p.is_file() and str(p.relative_to(D)) not in EX:
   b=p.read_bytes();files.append({'path':str(p.relative_to(D)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
 (D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':EX,'files':files},indent=2)+'\n');b=(D/'manifest.json').read_bytes();return {'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)}
(D/'negative-test-results.json').write_text('{}\n');(D/'final-verification-receipt.json').write_text('{}\n');pin=manifest()
# Local-lane payload only. Never copy corpus or upstream trees.
with tempfile.TemporaryDirectory(prefix='.negative-',dir=D) as td:
 T=pathlib.Path(td)
 for p in list(D.iterdir()):
  if p.is_file():shutil.copyfile(p,T/p.name)
 out=[];p=T/'reading.txt';original=p.read_bytes()
 for kind in ['hash','size','extra_file']:
  if kind=='hash':p.write_bytes(bytes([original[0]^1])+original[1:])
  if kind=='size':p.write_bytes(original+b'x')
  if kind=='extra_file':(T/'unexpected-payload').write_text('x')
  r=subprocess.run([sys.executable,'-B',str(T/'verify.py'),pin['sha256'],str(pin['size'])],capture_output=True,text=True)
  assert r.returncode!=0,(kind,r.stdout,r.stderr)
  expect={'hash':'hash mismatch','size':'size mismatch','extra_file':'extra/missing file mismatch'}[kind];assert expect in r.stderr,r.stderr
  out.append({'test':kind,'exit_code':r.returncode,'stderr':r.stderr.strip(),'originals_mutated':False})
  p.write_bytes(original)
  if (T/'unexpected-payload').exists():(T/'unexpected-payload').unlink()
(D/'negative-test-results.json').write_text(json.dumps(out,indent=2)+'\n');pin=manifest()
r=subprocess.run([sys.executable,'-B',str(D/'verify.py'),pin['sha256'],str(pin['size'])],capture_output=True,text=True)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':pin,'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'scope':'Independent read-only exact integrity, not mathematical/novelty PASS','guard':'fixed helper_guard.py; unchanged512MiBAS/groupRSS,CPU210s,wall230s','negative_tests':out}
(D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));assert r.returncode==0
