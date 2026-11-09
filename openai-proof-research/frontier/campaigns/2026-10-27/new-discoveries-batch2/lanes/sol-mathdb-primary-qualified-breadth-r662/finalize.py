import pathlib,json,hashlib,tempfile,subprocess,sys,datetime
O=pathlib.Path(__file__).resolve().parent
EX=['manifest.json','final-verification-receipt.json']
def bind(p,root):
 d=p.read_bytes();return dict(path=str(p.relative_to(root)),sha256=hashlib.sha256(d).hexdigest(),size=len(d))
results=[]
with tempfile.TemporaryDirectory(prefix='negative-fixture-',dir=O) as t:
 root=pathlib.Path(t);f=root/'sample.txt';f.write_bytes(b'abcd');m={'excluded_exact_paths':EX,'files':[bind(f,root)]};(root/'manifest.json').write_text(json.dumps(m))
 for kind in ['valid','hash','size','extra-file']:
  f.write_bytes(b'abcd')
  if kind=='hash':f.write_bytes(b'abce')
  if kind=='size':f.write_bytes(b'abcde')
  if kind=='extra-file':(root/'unexpected').write_text('x')
  r=subprocess.run([sys.executable,'-B',str(O/'verify.py'),'--payload-only',str(root)],capture_output=True,text=True)
  assert (r.returncode==0)==(kind=='valid'),(kind,r.stdout,r.stderr)
  results.append({'case':kind,'exit_code':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip(),'originals_mutated':False})
(O/'negative-tests.json').write_text(json.dumps(results,indent=2)+'\n')
m={'excluded_exact_paths':EX,'files':[bind(p,O) for p in sorted(O.rglob('*')) if p.is_file() and str(p.relative_to(O)) not in EX]}
(O/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
r=subprocess.run([sys.executable,'-B',str(O/'verify.py')],capture_output=True,text=True)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'guard':'fixed helper_guard.py,512MiB AS/groupRSS,CPU210s,wall230s; all Python including this finalizer guarded','manifest':bind(O/'manifest.json',O),'exit_code':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip(),'negative_tests':results,'integrity_is_not_math_or_novelty_pass':True}
(O/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));sys.exit(r.returncode)
